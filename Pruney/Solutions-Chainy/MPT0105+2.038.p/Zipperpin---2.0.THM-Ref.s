%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sADxCH6R2P

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:09 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 153 expanded)
%              Number of leaves         :   17 (  56 expanded)
%              Depth                    :   17
%              Number of atoms          :  655 (1188 expanded)
%              Number of equality atoms :   76 ( 145 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['34','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','43'])).

thf('45',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('46',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','57'])).

thf('59',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('62',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','63'])).

thf('65',plain,(
    $false ),
    inference(simplify,[status(thm)],['64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sADxCH6R2P
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:37:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 328 iterations in 0.148s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(t98_xboole_1, conjecture,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i,B:$i]:
% 0.39/0.61        ( ( k2_xboole_0 @ A @ B ) =
% 0.39/0.61          ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t98_xboole_1])).
% 0.39/0.61  thf('0', plain,
% 0.39/0.61      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.39/0.61         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(t3_boole, axiom,
% 0.39/0.61    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.61  thf('1', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.39/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.61  thf(t48_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.61  thf('2', plain,
% 0.39/0.61      (![X7 : $i, X8 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.39/0.61           = (k3_xboole_0 @ X7 @ X8))),
% 0.39/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.61  thf('3', plain,
% 0.39/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['1', '2'])).
% 0.39/0.61  thf(t2_boole, axiom,
% 0.39/0.61    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.39/0.61  thf('4', plain,
% 0.39/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.61      inference('cnf', [status(esa)], [t2_boole])).
% 0.39/0.61  thf('5', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.61      inference('demod', [status(thm)], ['3', '4'])).
% 0.39/0.61  thf(t39_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.61  thf('6', plain,
% 0.39/0.61      (![X1 : $i, X2 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X1))
% 0.39/0.61           = (k2_xboole_0 @ X1 @ X2))),
% 0.39/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.61  thf('7', plain,
% 0.39/0.61      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['5', '6'])).
% 0.39/0.61  thf('8', plain,
% 0.39/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.61      inference('cnf', [status(esa)], [t2_boole])).
% 0.39/0.61  thf(t94_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( k2_xboole_0 @ A @ B ) =
% 0.39/0.61       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.61  thf('9', plain,
% 0.39/0.61      (![X22 : $i, X23 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X22 @ X23)
% 0.39/0.61           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 0.39/0.61              (k3_xboole_0 @ X22 @ X23)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.39/0.61  thf(t91_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.61       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.39/0.61  thf('10', plain,
% 0.39/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.61         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.39/0.61           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.39/0.61  thf('11', plain,
% 0.39/0.61      (![X22 : $i, X23 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X22 @ X23)
% 0.39/0.61           = (k5_xboole_0 @ X22 @ 
% 0.39/0.61              (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X22 @ X23))))),
% 0.39/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.61  thf('12', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.39/0.61           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['8', '11'])).
% 0.39/0.61  thf(t5_boole, axiom,
% 0.39/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.61  thf('13', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.39/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.39/0.61  thf('14', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.61      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.61  thf('15', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.39/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.39/0.61  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.39/0.61  thf('17', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.39/0.61      inference('demod', [status(thm)], ['7', '16'])).
% 0.39/0.61  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.61      inference('demod', [status(thm)], ['3', '4'])).
% 0.39/0.61  thf(t41_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.61       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.61  thf('19', plain,
% 0.39/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 0.39/0.61           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.61  thf('20', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.61           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['18', '19'])).
% 0.39/0.61  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.39/0.61  thf('22', plain,
% 0.39/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 0.39/0.61           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.61  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.61      inference('demod', [status(thm)], ['3', '4'])).
% 0.39/0.61  thf('24', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.39/0.61           = (k1_xboole_0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['22', '23'])).
% 0.39/0.61  thf('25', plain,
% 0.39/0.61      (![X1 : $i, X2 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X1))
% 0.39/0.61           = (k2_xboole_0 @ X1 @ X2))),
% 0.39/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.61  thf('26', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.39/0.61      inference('demod', [status(thm)], ['24', '25'])).
% 0.39/0.61  thf('27', plain,
% 0.39/0.61      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['21', '26'])).
% 0.39/0.61  thf('28', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.61      inference('demod', [status(thm)], ['20', '27'])).
% 0.39/0.61  thf('29', plain,
% 0.39/0.61      (![X7 : $i, X8 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.39/0.61           = (k3_xboole_0 @ X7 @ X8))),
% 0.39/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.61  thf('30', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.39/0.61           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['28', '29'])).
% 0.39/0.61  thf('31', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.39/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.61  thf('32', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.61      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.61  thf(t52_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.39/0.61       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.39/0.61  thf('33', plain,
% 0.39/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 0.39/0.61           = (k2_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X11)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.39/0.61  thf('34', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))
% 0.39/0.61           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['32', '33'])).
% 0.39/0.61  thf('35', plain,
% 0.39/0.61      (![X7 : $i, X8 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.39/0.61           = (k3_xboole_0 @ X7 @ X8))),
% 0.39/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.61  thf('36', plain,
% 0.39/0.61      (![X1 : $i, X2 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X1))
% 0.39/0.61           = (k2_xboole_0 @ X1 @ X2))),
% 0.39/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.61  thf('37', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.61           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.39/0.61      inference('sup+', [status(thm)], ['35', '36'])).
% 0.39/0.61  thf('38', plain,
% 0.39/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 0.39/0.61           = (k2_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X11)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.39/0.61  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.61      inference('demod', [status(thm)], ['3', '4'])).
% 0.39/0.61  thf('40', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.39/0.61           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.39/0.61      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.39/0.61  thf('41', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.39/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.61  thf('42', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((X1) = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.39/0.61      inference('demod', [status(thm)], ['40', '41'])).
% 0.39/0.61  thf('43', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))
% 0.39/0.61           = (X0))),
% 0.39/0.61      inference('demod', [status(thm)], ['34', '42'])).
% 0.39/0.61  thf('44', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['17', '43'])).
% 0.39/0.61  thf('45', plain,
% 0.39/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 0.39/0.61           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.61  thf('46', plain,
% 0.39/0.61      (![X1 : $i, X2 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X1))
% 0.39/0.61           = (k2_xboole_0 @ X1 @ X2))),
% 0.39/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.61  thf('47', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.39/0.61           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['45', '46'])).
% 0.39/0.61  thf('48', plain,
% 0.39/0.61      (![X7 : $i, X8 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.39/0.61           = (k3_xboole_0 @ X7 @ X8))),
% 0.39/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.61  thf('49', plain,
% 0.39/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 0.39/0.61           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.61  thf('50', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.39/0.61           = (k4_xboole_0 @ X2 @ 
% 0.39/0.61              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.39/0.61      inference('sup+', [status(thm)], ['48', '49'])).
% 0.39/0.61  thf('51', plain,
% 0.39/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 0.39/0.61           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.61  thf('52', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.39/0.61           = (k4_xboole_0 @ X2 @ 
% 0.39/0.61              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.39/0.61      inference('demod', [status(thm)], ['50', '51'])).
% 0.39/0.61  thf('53', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.39/0.61           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.39/0.61      inference('sup+', [status(thm)], ['47', '52'])).
% 0.39/0.61  thf('54', plain,
% 0.39/0.61      (![X1 : $i, X2 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X1))
% 0.39/0.61           = (k2_xboole_0 @ X1 @ X2))),
% 0.39/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.61  thf('55', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.39/0.61           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.39/0.61      inference('demod', [status(thm)], ['53', '54'])).
% 0.39/0.61  thf('56', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.39/0.61      inference('demod', [status(thm)], ['24', '25'])).
% 0.39/0.61  thf('57', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.39/0.61      inference('demod', [status(thm)], ['55', '56'])).
% 0.39/0.61  thf('58', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['44', '57'])).
% 0.39/0.61  thf('59', plain,
% 0.39/0.61      (![X22 : $i, X23 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X22 @ X23)
% 0.39/0.61           = (k5_xboole_0 @ X22 @ 
% 0.39/0.61              (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X22 @ X23))))),
% 0.39/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.61  thf('60', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.39/0.61           = (k5_xboole_0 @ X0 @ 
% 0.39/0.61              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['58', '59'])).
% 0.39/0.61  thf('61', plain,
% 0.39/0.61      (![X1 : $i, X2 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X1))
% 0.39/0.61           = (k2_xboole_0 @ X1 @ X2))),
% 0.39/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.61  thf('62', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.39/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.39/0.61  thf('63', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X0 @ X1)
% 0.39/0.61           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.61      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.39/0.61  thf('64', plain,
% 0.39/0.61      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.61      inference('demod', [status(thm)], ['0', '63'])).
% 0.39/0.61  thf('65', plain, ($false), inference('simplify', [status(thm)], ['64'])).
% 0.39/0.61  
% 0.39/0.61  % SZS output end Refutation
% 0.39/0.61  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
