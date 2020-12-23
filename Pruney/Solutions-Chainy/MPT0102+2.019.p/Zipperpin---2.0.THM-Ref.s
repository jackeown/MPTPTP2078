%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hu1ZI1y0Kn

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:00 EST 2020

% Result     : Theorem 56.05s
% Output     : Refutation 56.05s
% Verified   : 
% Statistics : Number of formulae       :  197 (1254 expanded)
%              Number of leaves         :   19 ( 434 expanded)
%              Depth                    :   19
%              Number of atoms          : 1766 (9357 expanded)
%              Number of equality atoms :  189 (1246 expanded)
%              Maximal formula depth    :   12 (   7 average)

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

thf(t95_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

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

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('36',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('55',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','44','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','58'])).

thf('60',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['59','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('75',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('83',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','89','90','91'])).

thf('93',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('95',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','58'])).

thf('99',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','92','93','94','95','96','97','98','99','100'])).

thf('102',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('103',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','31'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('114',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','117'])).

thf('119',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('121',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['118','119','120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('124',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('125',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('129',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['122','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['118','119','120','121'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('135',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('136',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('137',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','31'])).

thf('141',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['138','139','140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['135','142'])).

thf('144',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['134','146'])).

thf('148',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('149',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['147','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('153',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('154',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['155','158','159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['152','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','22'])).

thf('165',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','22'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['131','132','133','151','162','163','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['111','172'])).

thf('174',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('175',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','173','174'])).

thf('176',plain,(
    $false ),
    inference(simplify,[status(thm)],['175'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hu1ZI1y0Kn
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 56.05/56.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 56.05/56.28  % Solved by: fo/fo7.sh
% 56.05/56.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 56.05/56.28  % done 16202 iterations in 55.828s
% 56.05/56.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 56.05/56.28  % SZS output start Refutation
% 56.05/56.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 56.05/56.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 56.05/56.28  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 56.05/56.28  thf(sk_A_type, type, sk_A: $i).
% 56.05/56.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 56.05/56.28  thf(sk_B_type, type, sk_B: $i).
% 56.05/56.28  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 56.05/56.28  thf(t95_xboole_1, conjecture,
% 56.05/56.28    (![A:$i,B:$i]:
% 56.05/56.28     ( ( k3_xboole_0 @ A @ B ) =
% 56.05/56.28       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 56.05/56.28  thf(zf_stmt_0, negated_conjecture,
% 56.05/56.28    (~( ![A:$i,B:$i]:
% 56.05/56.28        ( ( k3_xboole_0 @ A @ B ) =
% 56.05/56.28          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 56.05/56.28    inference('cnf.neg', [status(esa)], [t95_xboole_1])).
% 56.05/56.29  thf('0', plain,
% 56.05/56.29      (((k3_xboole_0 @ sk_A @ sk_B)
% 56.05/56.29         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 56.05/56.29             (k2_xboole_0 @ sk_A @ sk_B)))),
% 56.05/56.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.05/56.29  thf(d6_xboole_0, axiom,
% 56.05/56.29    (![A:$i,B:$i]:
% 56.05/56.29     ( ( k5_xboole_0 @ A @ B ) =
% 56.05/56.29       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 56.05/56.29  thf('1', plain,
% 56.05/56.29      (![X4 : $i, X5 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X4 @ X5)
% 56.05/56.29           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 56.05/56.29      inference('cnf', [status(esa)], [d6_xboole_0])).
% 56.05/56.29  thf(commutativity_k2_xboole_0, axiom,
% 56.05/56.29    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 56.05/56.29  thf('2', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 56.05/56.29  thf('3', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k5_xboole_0 @ X1 @ X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['1', '2'])).
% 56.05/56.29  thf('4', plain,
% 56.05/56.29      (![X4 : $i, X5 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X4 @ X5)
% 56.05/56.29           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 56.05/56.29      inference('cnf', [status(esa)], [d6_xboole_0])).
% 56.05/56.29  thf('5', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['3', '4'])).
% 56.05/56.29  thf(t41_xboole_1, axiom,
% 56.05/56.29    (![A:$i,B:$i,C:$i]:
% 56.05/56.29     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 56.05/56.29       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 56.05/56.29  thf('6', plain,
% 56.05/56.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 56.05/56.29           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 56.05/56.29      inference('cnf', [status(esa)], [t41_xboole_1])).
% 56.05/56.29  thf('7', plain,
% 56.05/56.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 56.05/56.29           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 56.05/56.29      inference('cnf', [status(esa)], [t41_xboole_1])).
% 56.05/56.29  thf('8', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 56.05/56.29           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['6', '7'])).
% 56.05/56.29  thf('9', plain,
% 56.05/56.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 56.05/56.29           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 56.05/56.29      inference('cnf', [status(esa)], [t41_xboole_1])).
% 56.05/56.29  thf('10', plain,
% 56.05/56.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 56.05/56.29           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 56.05/56.29      inference('cnf', [status(esa)], [t41_xboole_1])).
% 56.05/56.29  thf('11', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 56.05/56.29           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 56.05/56.29      inference('demod', [status(thm)], ['8', '9', '10'])).
% 56.05/56.29  thf('12', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 56.05/56.29  thf(t3_boole, axiom,
% 56.05/56.29    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 56.05/56.29  thf('13', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 56.05/56.29      inference('cnf', [status(esa)], [t3_boole])).
% 56.05/56.29  thf(t48_xboole_1, axiom,
% 56.05/56.29    (![A:$i,B:$i]:
% 56.05/56.29     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 56.05/56.29  thf('14', plain,
% 56.05/56.29      (![X17 : $i, X18 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 56.05/56.29           = (k3_xboole_0 @ X17 @ X18))),
% 56.05/56.29      inference('cnf', [status(esa)], [t48_xboole_1])).
% 56.05/56.29  thf('15', plain,
% 56.05/56.29      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['13', '14'])).
% 56.05/56.29  thf('16', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 56.05/56.29  thf(t1_boole, axiom,
% 56.05/56.29    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 56.05/56.29  thf('17', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 56.05/56.29      inference('cnf', [status(esa)], [t1_boole])).
% 56.05/56.29  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['16', '17'])).
% 56.05/56.29  thf(t22_xboole_1, axiom,
% 56.05/56.29    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 56.05/56.29  thf('19', plain,
% 56.05/56.29      (![X7 : $i, X8 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 56.05/56.29      inference('cnf', [status(esa)], [t22_xboole_1])).
% 56.05/56.29  thf('20', plain,
% 56.05/56.29      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['18', '19'])).
% 56.05/56.29  thf(commutativity_k3_xboole_0, axiom,
% 56.05/56.29    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 56.05/56.29  thf('21', plain,
% 56.05/56.29      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 56.05/56.29  thf('22', plain,
% 56.05/56.29      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['20', '21'])).
% 56.05/56.29  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 56.05/56.29      inference('demod', [status(thm)], ['15', '22'])).
% 56.05/56.29  thf('24', plain,
% 56.05/56.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 56.05/56.29           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 56.05/56.29      inference('cnf', [status(esa)], [t41_xboole_1])).
% 56.05/56.29  thf('25', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 56.05/56.29           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['23', '24'])).
% 56.05/56.29  thf('26', plain,
% 56.05/56.29      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['18', '19'])).
% 56.05/56.29  thf(t51_xboole_1, axiom,
% 56.05/56.29    (![A:$i,B:$i]:
% 56.05/56.29     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 56.05/56.29       ( A ) ))).
% 56.05/56.29  thf('27', plain,
% 56.05/56.29      (![X19 : $i, X20 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20))
% 56.05/56.29           = (X19))),
% 56.05/56.29      inference('cnf', [status(esa)], [t51_xboole_1])).
% 56.05/56.29  thf('28', plain,
% 56.05/56.29      (![X0 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 56.05/56.29           = (k1_xboole_0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['26', '27'])).
% 56.05/56.29  thf('29', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['16', '17'])).
% 56.05/56.29  thf('30', plain,
% 56.05/56.29      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 56.05/56.29      inference('demod', [status(thm)], ['28', '29'])).
% 56.05/56.29  thf('31', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('demod', [status(thm)], ['25', '30'])).
% 56.05/56.29  thf('32', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['12', '31'])).
% 56.05/56.29  thf('33', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.05/56.29         ((k1_xboole_0)
% 56.05/56.29           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 56.05/56.29      inference('sup+', [status(thm)], ['11', '32'])).
% 56.05/56.29  thf('34', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k5_xboole_0 @ X1 @ X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['1', '2'])).
% 56.05/56.29  thf(t40_xboole_1, axiom,
% 56.05/56.29    (![A:$i,B:$i]:
% 56.05/56.29     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 56.05/56.29  thf('35', plain,
% 56.05/56.29      (![X10 : $i, X11 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 56.05/56.29           = (k4_xboole_0 @ X10 @ X11))),
% 56.05/56.29      inference('cnf', [status(esa)], [t40_xboole_1])).
% 56.05/56.29  thf('36', plain,
% 56.05/56.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 56.05/56.29           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 56.05/56.29      inference('cnf', [status(esa)], [t41_xboole_1])).
% 56.05/56.29  thf('37', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 56.05/56.29           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['35', '36'])).
% 56.05/56.29  thf('38', plain,
% 56.05/56.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 56.05/56.29           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 56.05/56.29      inference('cnf', [status(esa)], [t41_xboole_1])).
% 56.05/56.29  thf('39', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 56.05/56.29           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 56.05/56.29      inference('demod', [status(thm)], ['37', '38'])).
% 56.05/56.29  thf('40', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 56.05/56.29           (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 56.05/56.29           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 56.05/56.29              (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['34', '39'])).
% 56.05/56.29  thf('41', plain,
% 56.05/56.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 56.05/56.29           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 56.05/56.29      inference('cnf', [status(esa)], [t41_xboole_1])).
% 56.05/56.29  thf('42', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X0 @ 
% 56.05/56.29           (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))
% 56.05/56.29           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 56.05/56.29              (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 56.05/56.29      inference('demod', [status(thm)], ['40', '41'])).
% 56.05/56.29  thf('43', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k1_xboole_0)
% 56.05/56.29           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 56.05/56.29              (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['33', '42'])).
% 56.05/56.29  thf('44', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 56.05/56.29  thf('45', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('demod', [status(thm)], ['25', '30'])).
% 56.05/56.29  thf('46', plain,
% 56.05/56.29      (![X17 : $i, X18 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 56.05/56.29           = (k3_xboole_0 @ X17 @ X18))),
% 56.05/56.29      inference('cnf', [status(esa)], [t48_xboole_1])).
% 56.05/56.29  thf('47', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 56.05/56.29           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['45', '46'])).
% 56.05/56.29  thf('48', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 56.05/56.29      inference('cnf', [status(esa)], [t3_boole])).
% 56.05/56.29  thf('49', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('demod', [status(thm)], ['47', '48'])).
% 56.05/56.29  thf('50', plain,
% 56.05/56.29      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 56.05/56.29  thf('51', plain,
% 56.05/56.29      (![X19 : $i, X20 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20))
% 56.05/56.29           = (X19))),
% 56.05/56.29      inference('cnf', [status(esa)], [t51_xboole_1])).
% 56.05/56.29  thf('52', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 56.05/56.29           = (X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['50', '51'])).
% 56.05/56.29  thf('53', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 56.05/56.29           = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('sup+', [status(thm)], ['49', '52'])).
% 56.05/56.29  thf('54', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 56.05/56.29  thf('55', plain,
% 56.05/56.29      (![X10 : $i, X11 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 56.05/56.29           = (k4_xboole_0 @ X10 @ X11))),
% 56.05/56.29      inference('cnf', [status(esa)], [t40_xboole_1])).
% 56.05/56.29  thf('56', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 56.05/56.29           = (k4_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('sup+', [status(thm)], ['54', '55'])).
% 56.05/56.29  thf('57', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('demod', [status(thm)], ['53', '56'])).
% 56.05/56.29  thf('58', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k1_xboole_0)
% 56.05/56.29           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 56.05/56.29      inference('demod', [status(thm)], ['43', '44', '57'])).
% 56.05/56.29  thf('59', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k1_xboole_0)
% 56.05/56.29           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['5', '58'])).
% 56.05/56.29  thf('60', plain,
% 56.05/56.29      (![X17 : $i, X18 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 56.05/56.29           = (k3_xboole_0 @ X17 @ X18))),
% 56.05/56.29      inference('cnf', [status(esa)], [t48_xboole_1])).
% 56.05/56.29  thf('61', plain,
% 56.05/56.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 56.05/56.29           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 56.05/56.29      inference('cnf', [status(esa)], [t41_xboole_1])).
% 56.05/56.29  thf('62', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.05/56.29         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 56.05/56.29           = (k4_xboole_0 @ X2 @ 
% 56.05/56.29              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 56.05/56.29      inference('sup+', [status(thm)], ['60', '61'])).
% 56.05/56.29  thf('63', plain,
% 56.05/56.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 56.05/56.29           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 56.05/56.29      inference('cnf', [status(esa)], [t41_xboole_1])).
% 56.05/56.29  thf('64', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.05/56.29         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 56.05/56.29           = (k4_xboole_0 @ X2 @ 
% 56.05/56.29              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 56.05/56.29      inference('demod', [status(thm)], ['62', '63'])).
% 56.05/56.29  thf('65', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('demod', [status(thm)], ['53', '56'])).
% 56.05/56.29  thf('66', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ 
% 56.05/56.29           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))) @ 
% 56.05/56.29           (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 56.05/56.29           = (k2_xboole_0 @ 
% 56.05/56.29              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))) @ 
% 56.05/56.29              X2))),
% 56.05/56.29      inference('sup+', [status(thm)], ['64', '65'])).
% 56.05/56.29  thf('67', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 56.05/56.29  thf('68', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 56.05/56.29  thf('69', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 56.05/56.29           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 56.05/56.29           = (k2_xboole_0 @ X2 @ 
% 56.05/56.29              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 56.05/56.29      inference('demod', [status(thm)], ['66', '67', '68'])).
% 56.05/56.29  thf('70', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ 
% 56.05/56.29           (k3_xboole_0 @ (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1) @ X0) @ 
% 56.05/56.29           (k2_xboole_0 @ X1 @ k1_xboole_0))
% 56.05/56.29           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 56.05/56.29              (k2_xboole_0 @ X1 @ 
% 56.05/56.29               (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))))),
% 56.05/56.29      inference('sup+', [status(thm)], ['59', '69'])).
% 56.05/56.29  thf('71', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 56.05/56.29  thf('72', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('demod', [status(thm)], ['47', '48'])).
% 56.05/56.29  thf('73', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['71', '72'])).
% 56.05/56.29  thf('74', plain,
% 56.05/56.29      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 56.05/56.29  thf('75', plain,
% 56.05/56.29      (![X7 : $i, X8 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 56.05/56.29      inference('cnf', [status(esa)], [t22_xboole_1])).
% 56.05/56.29  thf('76', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['74', '75'])).
% 56.05/56.29  thf('77', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 56.05/56.29           = (k2_xboole_0 @ X1 @ X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['73', '76'])).
% 56.05/56.29  thf('78', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 56.05/56.29  thf('79', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k2_xboole_0 @ X1 @ X0))),
% 56.05/56.29      inference('demod', [status(thm)], ['77', '78'])).
% 56.05/56.29  thf('80', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X0 @ 
% 56.05/56.29           (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))
% 56.05/56.29           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 56.05/56.29              (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 56.05/56.29      inference('demod', [status(thm)], ['40', '41'])).
% 56.05/56.29  thf('81', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))
% 56.05/56.29           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ 
% 56.05/56.29              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['79', '80'])).
% 56.05/56.29  thf('82', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 56.05/56.29  thf('83', plain,
% 56.05/56.29      (![X19 : $i, X20 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20))
% 56.05/56.29           = (X19))),
% 56.05/56.29      inference('cnf', [status(esa)], [t51_xboole_1])).
% 56.05/56.29  thf('84', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['71', '72'])).
% 56.05/56.29  thf('85', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X0 @ X1)
% 56.05/56.29           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['83', '84'])).
% 56.05/56.29  thf('86', plain,
% 56.05/56.29      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 56.05/56.29  thf('87', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X0 @ X1)
% 56.05/56.29           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 56.05/56.29      inference('demod', [status(thm)], ['85', '86'])).
% 56.05/56.29  thf('88', plain,
% 56.05/56.29      (![X7 : $i, X8 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 56.05/56.29      inference('cnf', [status(esa)], [t22_xboole_1])).
% 56.05/56.29  thf('89', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 56.05/56.29      inference('sup+', [status(thm)], ['87', '88'])).
% 56.05/56.29  thf('90', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 56.05/56.29  thf('91', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 56.05/56.29      inference('sup+', [status(thm)], ['87', '88'])).
% 56.05/56.29  thf('92', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X1 @ X0)
% 56.05/56.29           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0))),
% 56.05/56.29      inference('demod', [status(thm)], ['81', '82', '89', '90', '91'])).
% 56.05/56.29  thf('93', plain,
% 56.05/56.29      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 56.05/56.29  thf('94', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X0 @ X1)
% 56.05/56.29           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 56.05/56.29      inference('demod', [status(thm)], ['85', '86'])).
% 56.05/56.29  thf('95', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 56.05/56.29      inference('cnf', [status(esa)], [t1_boole])).
% 56.05/56.29  thf('96', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 56.05/56.29  thf('97', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('demod', [status(thm)], ['53', '56'])).
% 56.05/56.29  thf('98', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k1_xboole_0)
% 56.05/56.29           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['5', '58'])).
% 56.05/56.29  thf('99', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 56.05/56.29      inference('cnf', [status(esa)], [t1_boole])).
% 56.05/56.29  thf('100', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 56.05/56.29  thf('101', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ X1 @ X0)
% 56.05/56.29           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('demod', [status(thm)],
% 56.05/56.29                ['70', '92', '93', '94', '95', '96', '97', '98', '99', '100'])).
% 56.05/56.29  thf('102', plain,
% 56.05/56.29      (![X10 : $i, X11 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 56.05/56.29           = (k4_xboole_0 @ X10 @ X11))),
% 56.05/56.29      inference('cnf', [status(esa)], [t40_xboole_1])).
% 56.05/56.29  thf('103', plain,
% 56.05/56.29      (![X4 : $i, X5 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X4 @ X5)
% 56.05/56.29           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 56.05/56.29      inference('cnf', [status(esa)], [d6_xboole_0])).
% 56.05/56.29  thf('104', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 56.05/56.29              (k4_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['102', '103'])).
% 56.05/56.29  thf('105', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 56.05/56.29  thf('106', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 56.05/56.29              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 56.05/56.29      inference('demod', [status(thm)], ['104', '105'])).
% 56.05/56.29  thf('107', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['12', '31'])).
% 56.05/56.29  thf('108', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 56.05/56.29  thf('109', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['16', '17'])).
% 56.05/56.29  thf('110', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k4_xboole_0 @ X1 @ X0))),
% 56.05/56.29      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 56.05/56.29  thf('111', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['101', '110'])).
% 56.05/56.29  thf('112', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['71', '72'])).
% 56.05/56.29  thf('113', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 56.05/56.29           = (X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['50', '51'])).
% 56.05/56.29  thf('114', plain,
% 56.05/56.29      (![X10 : $i, X11 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 56.05/56.29           = (k4_xboole_0 @ X10 @ X11))),
% 56.05/56.29      inference('cnf', [status(esa)], [t40_xboole_1])).
% 56.05/56.29  thf('115', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 56.05/56.29           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['113', '114'])).
% 56.05/56.29  thf('116', plain,
% 56.05/56.29      (![X17 : $i, X18 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 56.05/56.29           = (k3_xboole_0 @ X17 @ X18))),
% 56.05/56.29      inference('cnf', [status(esa)], [t48_xboole_1])).
% 56.05/56.29  thf('117', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k3_xboole_0 @ X0 @ X1)
% 56.05/56.29           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 56.05/56.29      inference('demod', [status(thm)], ['115', '116'])).
% 56.05/56.29  thf('118', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 56.05/56.29           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['112', '117'])).
% 56.05/56.29  thf('119', plain,
% 56.05/56.29      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 56.05/56.29  thf('120', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['71', '72'])).
% 56.05/56.29  thf('121', plain,
% 56.05/56.29      (![X10 : $i, X11 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 56.05/56.29           = (k4_xboole_0 @ X10 @ X11))),
% 56.05/56.29      inference('cnf', [status(esa)], [t40_xboole_1])).
% 56.05/56.29  thf('122', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('demod', [status(thm)], ['118', '119', '120', '121'])).
% 56.05/56.29  thf('123', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k5_xboole_0 @ X1 @ X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['1', '2'])).
% 56.05/56.29  thf('124', plain,
% 56.05/56.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 56.05/56.29           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 56.05/56.29      inference('cnf', [status(esa)], [t41_xboole_1])).
% 56.05/56.29  thf('125', plain,
% 56.05/56.29      (![X4 : $i, X5 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X4 @ X5)
% 56.05/56.29           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 56.05/56.29      inference('cnf', [status(esa)], [d6_xboole_0])).
% 56.05/56.29  thf('126', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 56.05/56.29           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 56.05/56.29              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 56.05/56.29      inference('sup+', [status(thm)], ['124', '125'])).
% 56.05/56.29  thf('127', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 56.05/56.29           (k4_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 56.05/56.29              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 56.05/56.29               (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))))),
% 56.05/56.29      inference('sup+', [status(thm)], ['123', '126'])).
% 56.05/56.29  thf('128', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['3', '4'])).
% 56.05/56.29  thf('129', plain,
% 56.05/56.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 56.05/56.29           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 56.05/56.29      inference('cnf', [status(esa)], [t41_xboole_1])).
% 56.05/56.29  thf('130', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 56.05/56.29           (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 56.05/56.29           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 56.05/56.29              (k4_xboole_0 @ X1 @ 
% 56.05/56.29               (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))))))),
% 56.05/56.29      inference('demod', [status(thm)], ['127', '128', '129'])).
% 56.05/56.29  thf('131', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 56.05/56.29           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 56.05/56.29           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)) @ 
% 56.05/56.29              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 56.05/56.29      inference('sup+', [status(thm)], ['122', '130'])).
% 56.05/56.29  thf('132', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('demod', [status(thm)], ['118', '119', '120', '121'])).
% 56.05/56.29  thf('133', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['3', '4'])).
% 56.05/56.29  thf('134', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['74', '75'])).
% 56.05/56.29  thf('135', plain,
% 56.05/56.29      (![X10 : $i, X11 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 56.05/56.29           = (k4_xboole_0 @ X10 @ X11))),
% 56.05/56.29      inference('cnf', [status(esa)], [t40_xboole_1])).
% 56.05/56.29  thf('136', plain,
% 56.05/56.29      (![X17 : $i, X18 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 56.05/56.29           = (k3_xboole_0 @ X17 @ X18))),
% 56.05/56.29      inference('cnf', [status(esa)], [t48_xboole_1])).
% 56.05/56.29  thf('137', plain,
% 56.05/56.29      (![X4 : $i, X5 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X4 @ X5)
% 56.05/56.29           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 56.05/56.29      inference('cnf', [status(esa)], [d6_xboole_0])).
% 56.05/56.29  thf('138', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 56.05/56.29              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['136', '137'])).
% 56.05/56.29  thf('139', plain,
% 56.05/56.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 56.05/56.29           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 56.05/56.29      inference('cnf', [status(esa)], [t41_xboole_1])).
% 56.05/56.29  thf('140', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['12', '31'])).
% 56.05/56.29  thf('141', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 56.05/56.29      inference('cnf', [status(esa)], [t1_boole])).
% 56.05/56.29  thf('142', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k3_xboole_0 @ X1 @ X0))),
% 56.05/56.29      inference('demod', [status(thm)], ['138', '139', '140', '141'])).
% 56.05/56.29  thf('143', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['135', '142'])).
% 56.05/56.29  thf('144', plain,
% 56.05/56.29      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 56.05/56.29  thf('145', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['71', '72'])).
% 56.05/56.29  thf('146', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (X0))),
% 56.05/56.29      inference('demod', [status(thm)], ['143', '144', '145'])).
% 56.05/56.29  thf('147', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 56.05/56.29           = (k3_xboole_0 @ X1 @ X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['134', '146'])).
% 56.05/56.29  thf('148', plain,
% 56.05/56.29      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 56.05/56.29  thf(t47_xboole_1, axiom,
% 56.05/56.29    (![A:$i,B:$i]:
% 56.05/56.29     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 56.05/56.29  thf('149', plain,
% 56.05/56.29      (![X15 : $i, X16 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 56.05/56.29           = (k4_xboole_0 @ X15 @ X16))),
% 56.05/56.29      inference('cnf', [status(esa)], [t47_xboole_1])).
% 56.05/56.29  thf('150', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k4_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('sup+', [status(thm)], ['148', '149'])).
% 56.05/56.29  thf('151', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 56.05/56.29           = (k3_xboole_0 @ X1 @ X0))),
% 56.05/56.29      inference('demod', [status(thm)], ['147', '150'])).
% 56.05/56.29  thf('152', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['71', '72'])).
% 56.05/56.29  thf('153', plain,
% 56.05/56.29      (![X15 : $i, X16 : $i]:
% 56.05/56.29         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 56.05/56.29           = (k4_xboole_0 @ X15 @ X16))),
% 56.05/56.29      inference('cnf', [status(esa)], [t47_xboole_1])).
% 56.05/56.29  thf('154', plain,
% 56.05/56.29      (![X4 : $i, X5 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X4 @ X5)
% 56.05/56.29           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 56.05/56.29      inference('cnf', [status(esa)], [d6_xboole_0])).
% 56.05/56.29  thf('155', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 56.05/56.29              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['153', '154'])).
% 56.05/56.29  thf('156', plain,
% 56.05/56.29      (![X19 : $i, X20 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20))
% 56.05/56.29           = (X19))),
% 56.05/56.29      inference('cnf', [status(esa)], [t51_xboole_1])).
% 56.05/56.29  thf('157', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('demod', [status(thm)], ['25', '30'])).
% 56.05/56.29  thf('158', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['156', '157'])).
% 56.05/56.29  thf('159', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 56.05/56.29  thf('160', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['16', '17'])).
% 56.05/56.29  thf('161', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k4_xboole_0 @ X1 @ X0))),
% 56.05/56.29      inference('demod', [status(thm)], ['155', '158', '159', '160'])).
% 56.05/56.29  thf('162', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X0 @ X0)
% 56.05/56.29           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['152', '161'])).
% 56.05/56.29  thf('163', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 56.05/56.29  thf('164', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 56.05/56.29      inference('demod', [status(thm)], ['15', '22'])).
% 56.05/56.29  thf('165', plain,
% 56.05/56.29      (![X4 : $i, X5 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X4 @ X5)
% 56.05/56.29           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 56.05/56.29      inference('cnf', [status(esa)], [d6_xboole_0])).
% 56.05/56.29  thf('166', plain,
% 56.05/56.29      (![X0 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ X0 @ X0)
% 56.05/56.29           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)))),
% 56.05/56.29      inference('sup+', [status(thm)], ['164', '165'])).
% 56.05/56.29  thf('167', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 56.05/56.29      inference('demod', [status(thm)], ['15', '22'])).
% 56.05/56.29  thf('168', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['16', '17'])).
% 56.05/56.29  thf('169', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 56.05/56.29      inference('demod', [status(thm)], ['166', '167', '168'])).
% 56.05/56.29  thf('170', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 56.05/56.29      inference('sup+', [status(thm)], ['16', '17'])).
% 56.05/56.29  thf('171', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 56.05/56.29      inference('sup+', [status(thm)], ['169', '170'])).
% 56.05/56.29  thf('172', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k3_xboole_0 @ X1 @ X0)
% 56.05/56.29           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 56.05/56.29      inference('demod', [status(thm)],
% 56.05/56.29                ['131', '132', '133', '151', '162', '163', '171'])).
% 56.05/56.29  thf('173', plain,
% 56.05/56.29      (![X0 : $i, X1 : $i]:
% 56.05/56.29         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 56.05/56.29           = (k3_xboole_0 @ X0 @ X1))),
% 56.05/56.29      inference('demod', [status(thm)], ['111', '172'])).
% 56.05/56.29  thf('174', plain,
% 56.05/56.29      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 56.05/56.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 56.05/56.29  thf('175', plain,
% 56.05/56.29      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 56.05/56.29      inference('demod', [status(thm)], ['0', '173', '174'])).
% 56.05/56.29  thf('176', plain, ($false), inference('simplify', [status(thm)], ['175'])).
% 56.05/56.29  
% 56.05/56.29  % SZS output end Refutation
% 56.05/56.29  
% 56.09/56.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
