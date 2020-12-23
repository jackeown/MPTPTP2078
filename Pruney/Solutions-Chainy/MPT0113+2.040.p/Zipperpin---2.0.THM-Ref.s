%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zJJkJRhxcI

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:34 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 202 expanded)
%              Number of leaves         :   23 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  719 (1431 expanded)
%              Number of equality atoms :   78 ( 153 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

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

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['8','13'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('16',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X13 ) ) @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('24',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ X0 ) ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','38'])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','42'])).

thf('44',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['14','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('54',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['8','13'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('58',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('62',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('69',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['55','70'])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['52','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('76',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('78',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['49','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zJJkJRhxcI
% 0.11/0.33  % Computer   : n012.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 16:55:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.51/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.69  % Solved by: fo/fo7.sh
% 0.51/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.69  % done 783 iterations in 0.249s
% 0.51/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.69  % SZS output start Refutation
% 0.51/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.51/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.51/0.69  thf(t106_xboole_1, conjecture,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.51/0.69       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.51/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.69    (~( ![A:$i,B:$i,C:$i]:
% 0.51/0.69        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.51/0.69          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.51/0.69    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.51/0.69  thf('0', plain,
% 0.51/0.69      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('1', plain,
% 0.51/0.69      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.51/0.69      inference('split', [status(esa)], ['0'])).
% 0.51/0.69  thf(t79_xboole_1, axiom,
% 0.51/0.69    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.51/0.69  thf('2', plain,
% 0.51/0.69      (![X22 : $i, X23 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X23)),
% 0.51/0.69      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.51/0.69  thf(d7_xboole_0, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.51/0.69       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.51/0.69  thf('3', plain,
% 0.51/0.69      (![X2 : $i, X3 : $i]:
% 0.51/0.69         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.51/0.69      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.51/0.69  thf('4', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.51/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.51/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.51/0.69  thf('5', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.69  thf('6', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.51/0.69      inference('demod', [status(thm)], ['4', '5'])).
% 0.51/0.69  thf(t100_xboole_1, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.51/0.69  thf('7', plain,
% 0.51/0.69      (![X8 : $i, X9 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X8 @ X9)
% 0.51/0.69           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.51/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.69  thf('8', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.51/0.69           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['6', '7'])).
% 0.51/0.69  thf(t2_boole, axiom,
% 0.51/0.69    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.51/0.69  thf('9', plain,
% 0.51/0.69      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.51/0.69      inference('cnf', [status(esa)], [t2_boole])).
% 0.51/0.69  thf('10', plain,
% 0.51/0.69      (![X8 : $i, X9 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X8 @ X9)
% 0.51/0.69           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.51/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.69  thf('11', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['9', '10'])).
% 0.51/0.69  thf(t3_boole, axiom,
% 0.51/0.69    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.51/0.69  thf('12', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.51/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.51/0.69  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['11', '12'])).
% 0.51/0.69  thf('14', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.51/0.69      inference('demod', [status(thm)], ['8', '13'])).
% 0.51/0.69  thf(t52_xboole_1, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.51/0.69       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.51/0.69  thf('15', plain,
% 0.51/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.51/0.69           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 0.51/0.69              (k3_xboole_0 @ X19 @ X21)))),
% 0.51/0.69      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.51/0.69  thf('16', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf(l32_xboole_1, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.51/0.69  thf('17', plain,
% 0.51/0.69      (![X5 : $i, X7 : $i]:
% 0.51/0.69         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.51/0.69      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.51/0.69  thf('18', plain,
% 0.51/0.69      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.69  thf(t48_xboole_1, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.51/0.69  thf('19', plain,
% 0.51/0.69      (![X17 : $i, X18 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.51/0.69           = (k3_xboole_0 @ X17 @ X18))),
% 0.51/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.51/0.69  thf('20', plain,
% 0.51/0.69      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.51/0.69         = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('21', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.51/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.51/0.69  thf('22', plain,
% 0.51/0.69      (((sk_A) = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['20', '21'])).
% 0.51/0.69  thf(t31_xboole_1, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( r1_tarski @
% 0.51/0.69       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.51/0.69       ( k2_xboole_0 @ B @ C ) ))).
% 0.51/0.69  thf('23', plain,
% 0.51/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.51/0.69         (r1_tarski @ 
% 0.51/0.69          (k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k3_xboole_0 @ X11 @ X13)) @ 
% 0.51/0.69          (k2_xboole_0 @ X12 @ X13))),
% 0.51/0.69      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.51/0.69  thf('24', plain,
% 0.51/0.69      (![X5 : $i, X7 : $i]:
% 0.51/0.69         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.51/0.69      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.51/0.69  thf('25', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ 
% 0.51/0.69           (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X2 @ X0)) @ 
% 0.51/0.69           (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['23', '24'])).
% 0.51/0.69  thf('26', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ X0)) @ 
% 0.51/0.69           (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)) = (k1_xboole_0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['22', '25'])).
% 0.51/0.69  thf('27', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.51/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.51/0.69  thf('28', plain,
% 0.51/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.51/0.69           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 0.51/0.69              (k3_xboole_0 @ X19 @ X21)))),
% 0.51/0.69      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.51/0.69  thf('29', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 0.51/0.69           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['27', '28'])).
% 0.51/0.69  thf('30', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.69  thf('31', plain,
% 0.51/0.69      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.51/0.69      inference('cnf', [status(esa)], [t2_boole])).
% 0.51/0.69  thf('32', plain,
% 0.51/0.69      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['30', '31'])).
% 0.51/0.69  thf('33', plain,
% 0.51/0.69      (![X8 : $i, X9 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X8 @ X9)
% 0.51/0.69           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.51/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.69  thf('34', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.51/0.69           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['32', '33'])).
% 0.51/0.69  thf(t92_xboole_1, axiom,
% 0.51/0.69    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.51/0.69  thf('35', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 0.51/0.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.51/0.69  thf('36', plain,
% 0.51/0.69      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.51/0.69      inference('demod', [status(thm)], ['34', '35'])).
% 0.51/0.69  thf('37', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.51/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.51/0.69  thf('38', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.51/0.69      inference('demod', [status(thm)], ['29', '36', '37'])).
% 0.51/0.69  thf('39', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ sk_A @ 
% 0.51/0.69           (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)) = (k1_xboole_0))),
% 0.51/0.69      inference('demod', [status(thm)], ['26', '38'])).
% 0.51/0.69  thf('40', plain,
% 0.51/0.69      (![X5 : $i, X6 : $i]:
% 0.51/0.69         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.51/0.69      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.51/0.69  thf('41', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (((k1_xboole_0) != (k1_xboole_0))
% 0.51/0.69          | (r1_tarski @ sk_A @ 
% 0.51/0.69             (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['39', '40'])).
% 0.51/0.69  thf('42', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))),
% 0.51/0.69      inference('simplify', [status(thm)], ['41'])).
% 0.51/0.69  thf('43', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ X0)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['15', '42'])).
% 0.51/0.69  thf('44', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.51/0.69      inference('sup+', [status(thm)], ['14', '43'])).
% 0.51/0.69  thf('45', plain,
% 0.51/0.69      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.51/0.69      inference('split', [status(esa)], ['0'])).
% 0.51/0.69  thf('46', plain, (((r1_tarski @ sk_A @ sk_B))),
% 0.51/0.69      inference('sup-', [status(thm)], ['44', '45'])).
% 0.51/0.69  thf('47', plain,
% 0.51/0.69      (~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_tarski @ sk_A @ sk_B))),
% 0.51/0.69      inference('split', [status(esa)], ['0'])).
% 0.51/0.69  thf('48', plain, (~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.51/0.69      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 0.51/0.69  thf('49', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.51/0.69      inference('simpl_trail', [status(thm)], ['1', '48'])).
% 0.51/0.69  thf('50', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.51/0.69      inference('demod', [status(thm)], ['8', '13'])).
% 0.51/0.69  thf('51', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.51/0.69      inference('demod', [status(thm)], ['8', '13'])).
% 0.51/0.69  thf('52', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.51/0.69           = (k4_xboole_0 @ X1 @ X0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['50', '51'])).
% 0.51/0.69  thf('53', plain,
% 0.51/0.69      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.69  thf('54', plain,
% 0.51/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.51/0.69           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 0.51/0.69              (k3_xboole_0 @ X19 @ X21)))),
% 0.51/0.69      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.51/0.69  thf('55', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ sk_A @ 
% 0.51/0.69           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))
% 0.51/0.69           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['53', '54'])).
% 0.51/0.69  thf('56', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.51/0.69      inference('demod', [status(thm)], ['8', '13'])).
% 0.51/0.69  thf(t46_xboole_1, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.51/0.69  thf('57', plain,
% 0.51/0.69      (![X15 : $i, X16 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X15 @ X16)) = (k1_xboole_0))),
% 0.51/0.69      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.51/0.69  thf('58', plain,
% 0.51/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.51/0.69           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 0.51/0.69              (k3_xboole_0 @ X19 @ X21)))),
% 0.51/0.69      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.51/0.69  thf('59', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X0))
% 0.51/0.69           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['57', '58'])).
% 0.51/0.69  thf('60', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((X0) = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['56', '59'])).
% 0.51/0.69  thf('61', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.51/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.51/0.69  thf('62', plain,
% 0.51/0.69      (![X17 : $i, X18 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.51/0.69           = (k3_xboole_0 @ X17 @ X18))),
% 0.51/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.51/0.69  thf('63', plain,
% 0.51/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['61', '62'])).
% 0.51/0.69  thf('64', plain,
% 0.51/0.69      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.51/0.69      inference('cnf', [status(esa)], [t2_boole])).
% 0.51/0.69  thf('65', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.51/0.69      inference('demod', [status(thm)], ['63', '64'])).
% 0.51/0.69  thf('66', plain,
% 0.51/0.69      (![X17 : $i, X18 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.51/0.69           = (k3_xboole_0 @ X17 @ X18))),
% 0.51/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.51/0.69  thf('67', plain,
% 0.51/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['65', '66'])).
% 0.51/0.69  thf('68', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.51/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.51/0.69  thf('69', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.51/0.69      inference('demod', [status(thm)], ['67', '68'])).
% 0.51/0.69  thf('70', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.51/0.69      inference('demod', [status(thm)], ['60', '69'])).
% 0.51/0.69  thf('71', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((k4_xboole_0 @ sk_A @ 
% 0.51/0.69           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))
% 0.51/0.69           = (k3_xboole_0 @ sk_A @ X0))),
% 0.51/0.69      inference('demod', [status(thm)], ['55', '70'])).
% 0.51/0.69  thf('72', plain,
% 0.51/0.69      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.51/0.69         = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.51/0.69      inference('sup+', [status(thm)], ['52', '71'])).
% 0.51/0.69  thf('73', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.69  thf('74', plain,
% 0.51/0.69      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.51/0.69         = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['72', '73'])).
% 0.51/0.69  thf('75', plain,
% 0.51/0.69      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.69  thf('76', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.51/0.69      inference('sup+', [status(thm)], ['74', '75'])).
% 0.51/0.69  thf('77', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.69  thf('78', plain,
% 0.51/0.69      (![X2 : $i, X4 : $i]:
% 0.51/0.69         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.51/0.69      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.51/0.69  thf('79', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.51/0.69      inference('sup-', [status(thm)], ['77', '78'])).
% 0.51/0.69  thf('80', plain,
% 0.51/0.69      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.51/0.69      inference('sup-', [status(thm)], ['76', '79'])).
% 0.51/0.69  thf('81', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.51/0.69      inference('simplify', [status(thm)], ['80'])).
% 0.51/0.69  thf('82', plain, ($false), inference('demod', [status(thm)], ['49', '81'])).
% 0.51/0.69  
% 0.51/0.69  % SZS output end Refutation
% 0.51/0.69  
% 0.51/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
