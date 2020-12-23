%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CpMV5HWCoF

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:10 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 228 expanded)
%              Number of leaves         :   18 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          :  612 (1701 expanded)
%              Number of equality atoms :   73 ( 220 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t100_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t100_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['42','45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','48'])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','14','15','29','56','57','58'])).

thf('60',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','59'])).

thf('61',plain,(
    $false ),
    inference(simplify,[status(thm)],['60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CpMV5HWCoF
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:25:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.63  % Solved by: fo/fo7.sh
% 0.42/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.63  % done 277 iterations in 0.165s
% 0.42/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.63  % SZS output start Refutation
% 0.42/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.42/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.63  thf(t100_xboole_1, conjecture,
% 0.42/0.63    (![A:$i,B:$i]:
% 0.42/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.42/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.63    (~( ![A:$i,B:$i]:
% 0.42/0.63        ( ( k4_xboole_0 @ A @ B ) =
% 0.42/0.63          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.42/0.63    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.42/0.63  thf('0', plain,
% 0.42/0.63      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.42/0.63         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.42/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.42/0.63  thf('1', plain,
% 0.42/0.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.42/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.42/0.63  thf('2', plain,
% 0.42/0.63      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.42/0.63         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.42/0.63      inference('demod', [status(thm)], ['0', '1'])).
% 0.42/0.63  thf('3', plain,
% 0.42/0.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.42/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.42/0.63  thf(t47_xboole_1, axiom,
% 0.42/0.63    (![A:$i,B:$i]:
% 0.42/0.63     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.42/0.63  thf('4', plain,
% 0.42/0.63      (![X9 : $i, X10 : $i]:
% 0.42/0.63         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.42/0.63           = (k4_xboole_0 @ X9 @ X10))),
% 0.42/0.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.42/0.63  thf('5', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.42/0.63           = (k4_xboole_0 @ X0 @ X1))),
% 0.42/0.63      inference('sup+', [status(thm)], ['3', '4'])).
% 0.42/0.63  thf(d6_xboole_0, axiom,
% 0.42/0.63    (![A:$i,B:$i]:
% 0.42/0.63     ( ( k5_xboole_0 @ A @ B ) =
% 0.42/0.63       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.42/0.63  thf('6', plain,
% 0.42/0.63      (![X4 : $i, X5 : $i]:
% 0.42/0.63         ((k5_xboole_0 @ X4 @ X5)
% 0.42/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 0.42/0.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.42/0.63  thf('7', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)
% 0.42/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1) @ 
% 0.42/0.63              (k4_xboole_0 @ X1 @ X0)))),
% 0.42/0.63      inference('sup+', [status(thm)], ['5', '6'])).
% 0.42/0.63  thf(commutativity_k2_xboole_0, axiom,
% 0.42/0.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.42/0.63  thf('8', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.42/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.42/0.63  thf('9', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)
% 0.42/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.42/0.63              (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)))),
% 0.42/0.63      inference('demod', [status(thm)], ['7', '8'])).
% 0.42/0.63  thf('10', plain,
% 0.42/0.63      (![X4 : $i, X5 : $i]:
% 0.42/0.63         ((k5_xboole_0 @ X4 @ X5)
% 0.42/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 0.42/0.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.42/0.63  thf('11', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.42/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.42/0.63  thf('12', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 0.42/0.63           = (k5_xboole_0 @ X1 @ X0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['10', '11'])).
% 0.42/0.63  thf('13', plain,
% 0.42/0.63      (![X4 : $i, X5 : $i]:
% 0.42/0.63         ((k5_xboole_0 @ X4 @ X5)
% 0.42/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 0.42/0.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.42/0.63  thf('14', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['12', '13'])).
% 0.42/0.63  thf(t49_xboole_1, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i]:
% 0.42/0.63     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.42/0.63       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.42/0.63  thf('15', plain,
% 0.42/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.63         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.42/0.63           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.42/0.63      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.42/0.63  thf('16', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.42/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.42/0.63  thf(t1_boole, axiom,
% 0.42/0.63    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.42/0.63  thf('17', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.42/0.63      inference('cnf', [status(esa)], [t1_boole])).
% 0.42/0.63  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['16', '17'])).
% 0.42/0.63  thf(t39_xboole_1, axiom,
% 0.42/0.63    (![A:$i,B:$i]:
% 0.42/0.63     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.42/0.63  thf('19', plain,
% 0.42/0.63      (![X7 : $i, X8 : $i]:
% 0.42/0.63         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.42/0.63           = (k2_xboole_0 @ X7 @ X8))),
% 0.42/0.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.42/0.63  thf('20', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['18', '19'])).
% 0.42/0.63  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['16', '17'])).
% 0.42/0.63  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.42/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.42/0.63  thf(t48_xboole_1, axiom,
% 0.42/0.63    (![A:$i,B:$i]:
% 0.42/0.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.42/0.63  thf('23', plain,
% 0.42/0.63      (![X11 : $i, X12 : $i]:
% 0.42/0.63         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.42/0.63           = (k3_xboole_0 @ X11 @ X12))),
% 0.42/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.42/0.63  thf('24', plain,
% 0.42/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['22', '23'])).
% 0.42/0.63  thf('25', plain,
% 0.42/0.63      (![X4 : $i, X5 : $i]:
% 0.42/0.63         ((k5_xboole_0 @ X4 @ X5)
% 0.42/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 0.42/0.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.42/0.63  thf('26', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((k5_xboole_0 @ X0 @ X0)
% 0.42/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 0.42/0.63              (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.42/0.63      inference('sup+', [status(thm)], ['24', '25'])).
% 0.42/0.63  thf(t52_xboole_1, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i]:
% 0.42/0.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.42/0.63       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.42/0.63  thf('27', plain,
% 0.42/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.63         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.42/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ 
% 0.42/0.63              (k3_xboole_0 @ X18 @ X20)))),
% 0.42/0.63      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.42/0.63  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.42/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.42/0.63  thf('29', plain,
% 0.42/0.63      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.42/0.63      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.42/0.63  thf('30', plain,
% 0.42/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['22', '23'])).
% 0.42/0.63  thf('31', plain,
% 0.42/0.63      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.42/0.63      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.42/0.63  thf('32', plain,
% 0.42/0.63      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.42/0.63      inference('demod', [status(thm)], ['30', '31'])).
% 0.42/0.63  thf('33', plain,
% 0.42/0.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.42/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.42/0.63  thf('34', plain,
% 0.42/0.63      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['32', '33'])).
% 0.42/0.63  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.42/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.42/0.63  thf('36', plain,
% 0.42/0.63      (![X11 : $i, X12 : $i]:
% 0.42/0.63         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.42/0.63           = (k3_xboole_0 @ X11 @ X12))),
% 0.42/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.42/0.63  thf('37', plain,
% 0.42/0.63      (![X11 : $i, X12 : $i]:
% 0.42/0.63         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.42/0.63           = (k3_xboole_0 @ X11 @ X12))),
% 0.42/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.42/0.63  thf('38', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.42/0.63           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.42/0.63      inference('sup+', [status(thm)], ['36', '37'])).
% 0.42/0.63  thf('39', plain,
% 0.42/0.63      (![X9 : $i, X10 : $i]:
% 0.42/0.63         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.42/0.63           = (k4_xboole_0 @ X9 @ X10))),
% 0.42/0.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.42/0.63  thf('40', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.42/0.63           = (k4_xboole_0 @ X1 @ X0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['38', '39'])).
% 0.42/0.63  thf(t51_xboole_1, axiom,
% 0.42/0.63    (![A:$i,B:$i]:
% 0.42/0.63     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.42/0.63       ( A ) ))).
% 0.42/0.63  thf('41', plain,
% 0.42/0.63      (![X16 : $i, X17 : $i]:
% 0.42/0.63         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 0.42/0.63           = (X16))),
% 0.42/0.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.42/0.63  thf('42', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.42/0.63           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))) = (X1))),
% 0.42/0.63      inference('sup+', [status(thm)], ['40', '41'])).
% 0.42/0.63  thf('43', plain,
% 0.42/0.63      (![X9 : $i, X10 : $i]:
% 0.42/0.63         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.42/0.63           = (k4_xboole_0 @ X9 @ X10))),
% 0.42/0.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.42/0.63  thf('44', plain,
% 0.42/0.63      (![X11 : $i, X12 : $i]:
% 0.42/0.63         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.42/0.63           = (k3_xboole_0 @ X11 @ X12))),
% 0.42/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.42/0.63  thf('45', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.42/0.63           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.42/0.63      inference('sup+', [status(thm)], ['43', '44'])).
% 0.42/0.63  thf('46', plain,
% 0.42/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.63         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.42/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ 
% 0.42/0.63              (k3_xboole_0 @ X18 @ X20)))),
% 0.42/0.63      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.42/0.63  thf('47', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.42/0.63           = (k4_xboole_0 @ X0 @ X1))),
% 0.42/0.63      inference('sup+', [status(thm)], ['3', '4'])).
% 0.42/0.63  thf('48', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (X1))),
% 0.42/0.63      inference('demod', [status(thm)], ['42', '45', '46', '47'])).
% 0.42/0.63  thf('49', plain,
% 0.42/0.63      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['35', '48'])).
% 0.42/0.63  thf('50', plain,
% 0.42/0.63      (![X11 : $i, X12 : $i]:
% 0.42/0.63         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.42/0.63           = (k3_xboole_0 @ X11 @ X12))),
% 0.42/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.42/0.63  thf('51', plain,
% 0.42/0.63      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['49', '50'])).
% 0.42/0.63  thf('52', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.42/0.63      inference('demod', [status(thm)], ['34', '51'])).
% 0.42/0.63  thf('53', plain,
% 0.42/0.63      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['49', '50'])).
% 0.42/0.63  thf('54', plain,
% 0.42/0.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.42/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.42/0.63  thf('55', plain,
% 0.42/0.63      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['53', '54'])).
% 0.42/0.63  thf('56', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['52', '55'])).
% 0.42/0.63  thf('57', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.42/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.42/0.63  thf('58', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['16', '17'])).
% 0.42/0.63  thf('59', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.42/0.63           = (k4_xboole_0 @ X1 @ X0))),
% 0.42/0.63      inference('demod', [status(thm)],
% 0.42/0.63                ['9', '14', '15', '29', '56', '57', '58'])).
% 0.42/0.63  thf('60', plain,
% 0.42/0.63      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.42/0.63      inference('demod', [status(thm)], ['2', '59'])).
% 0.42/0.63  thf('61', plain, ($false), inference('simplify', [status(thm)], ['60'])).
% 0.42/0.63  
% 0.42/0.63  % SZS output end Refutation
% 0.42/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
