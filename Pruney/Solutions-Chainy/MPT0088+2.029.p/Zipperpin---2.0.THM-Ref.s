%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ID5kiMB8KI

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:38 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 372 expanded)
%              Number of leaves         :   17 ( 131 expanded)
%              Depth                    :   19
%              Number of atoms          :  791 (2856 expanded)
%              Number of equality atoms :   79 ( 329 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
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
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('17',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('26',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['19','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X0 ) ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['15','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','30'])).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','48'])).

thf('50',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('56',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','28'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf('62',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('65',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ X0 ) ) )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['52','66'])).

thf('68',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('71',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('75',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['51','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['0','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ID5kiMB8KI
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:15:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.50/1.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.50/1.78  % Solved by: fo/fo7.sh
% 1.50/1.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.50/1.78  % done 2264 iterations in 1.313s
% 1.50/1.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.50/1.78  % SZS output start Refutation
% 1.50/1.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.50/1.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.50/1.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.50/1.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.50/1.78  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.50/1.78  thf(sk_C_type, type, sk_C: $i).
% 1.50/1.78  thf(sk_B_type, type, sk_B: $i).
% 1.50/1.78  thf(sk_A_type, type, sk_A: $i).
% 1.50/1.78  thf(t81_xboole_1, conjecture,
% 1.50/1.78    (![A:$i,B:$i,C:$i]:
% 1.50/1.78     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.50/1.78       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 1.50/1.78  thf(zf_stmt_0, negated_conjecture,
% 1.50/1.78    (~( ![A:$i,B:$i,C:$i]:
% 1.50/1.78        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.50/1.78          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 1.50/1.78    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 1.50/1.78  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 1.50/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.78  thf(t3_boole, axiom,
% 1.50/1.78    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.50/1.78  thf('1', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.50/1.78      inference('cnf', [status(esa)], [t3_boole])).
% 1.50/1.78  thf(t48_xboole_1, axiom,
% 1.50/1.78    (![A:$i,B:$i]:
% 1.50/1.78     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.50/1.78  thf('2', plain,
% 1.50/1.78      (![X8 : $i, X9 : $i]:
% 1.50/1.78         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.50/1.78           = (k3_xboole_0 @ X8 @ X9))),
% 1.50/1.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.50/1.78  thf('3', plain,
% 1.50/1.78      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.50/1.78      inference('sup+', [status(thm)], ['1', '2'])).
% 1.50/1.78  thf(t2_boole, axiom,
% 1.50/1.78    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.50/1.78  thf('4', plain,
% 1.50/1.78      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 1.50/1.78      inference('cnf', [status(esa)], [t2_boole])).
% 1.50/1.78  thf('5', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.50/1.78      inference('demod', [status(thm)], ['3', '4'])).
% 1.50/1.78  thf(t41_xboole_1, axiom,
% 1.50/1.78    (![A:$i,B:$i,C:$i]:
% 1.50/1.78     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.50/1.78       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.50/1.78  thf('6', plain,
% 1.50/1.78      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.50/1.78         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 1.50/1.78           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 1.50/1.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.50/1.78  thf('7', plain,
% 1.50/1.78      (![X0 : $i, X1 : $i]:
% 1.50/1.78         ((k1_xboole_0)
% 1.50/1.78           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.50/1.78      inference('sup+', [status(thm)], ['5', '6'])).
% 1.50/1.78  thf(t79_xboole_1, axiom,
% 1.50/1.78    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.50/1.78  thf('8', plain,
% 1.50/1.78      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 1.50/1.78      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.50/1.78  thf(d7_xboole_0, axiom,
% 1.50/1.78    (![A:$i,B:$i]:
% 1.50/1.78     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.50/1.78       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.50/1.78  thf('9', plain,
% 1.50/1.78      (![X0 : $i, X1 : $i]:
% 1.50/1.78         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.50/1.78      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.50/1.78  thf('10', plain,
% 1.50/1.78      (![X0 : $i, X1 : $i]:
% 1.50/1.78         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.50/1.78      inference('sup-', [status(thm)], ['8', '9'])).
% 1.50/1.78  thf(t52_xboole_1, axiom,
% 1.50/1.78    (![A:$i,B:$i,C:$i]:
% 1.50/1.78     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.50/1.78       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.50/1.78  thf('11', plain,
% 1.50/1.78      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.50/1.78         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 1.50/1.78           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 1.50/1.78              (k3_xboole_0 @ X13 @ X15)))),
% 1.50/1.78      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.50/1.78  thf('12', plain,
% 1.50/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.78         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0))
% 1.50/1.78           = (k2_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ 
% 1.50/1.78              k1_xboole_0))),
% 1.50/1.78      inference('sup+', [status(thm)], ['10', '11'])).
% 1.50/1.78  thf('13', plain,
% 1.50/1.78      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.50/1.78         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 1.50/1.78           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 1.50/1.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.50/1.78  thf('14', plain,
% 1.50/1.78      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.50/1.78         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 1.50/1.78           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 1.50/1.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.50/1.78  thf('15', plain,
% 1.50/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.78         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X0)))
% 1.50/1.78           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)) @ 
% 1.50/1.78              k1_xboole_0))),
% 1.50/1.78      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.50/1.78  thf('16', plain,
% 1.50/1.78      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 1.50/1.78      inference('cnf', [status(esa)], [t2_boole])).
% 1.50/1.78  thf('17', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.50/1.78      inference('cnf', [status(esa)], [t3_boole])).
% 1.50/1.78  thf('18', plain,
% 1.50/1.78      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.50/1.78         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 1.50/1.78           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 1.50/1.78              (k3_xboole_0 @ X13 @ X15)))),
% 1.50/1.78      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.50/1.78  thf('19', plain,
% 1.50/1.78      (![X0 : $i, X1 : $i]:
% 1.50/1.78         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 1.50/1.78           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.50/1.78      inference('sup+', [status(thm)], ['17', '18'])).
% 1.50/1.78  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.50/1.78      inference('demod', [status(thm)], ['3', '4'])).
% 1.50/1.78  thf('21', plain,
% 1.50/1.78      (![X0 : $i, X1 : $i]:
% 1.50/1.78         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.50/1.78      inference('sup-', [status(thm)], ['8', '9'])).
% 1.50/1.78  thf('22', plain,
% 1.50/1.78      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.50/1.78      inference('sup+', [status(thm)], ['20', '21'])).
% 1.50/1.78  thf(t49_xboole_1, axiom,
% 1.50/1.78    (![A:$i,B:$i,C:$i]:
% 1.50/1.78     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.50/1.78       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.50/1.78  thf('23', plain,
% 1.50/1.78      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.50/1.78         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 1.50/1.78           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 1.50/1.78      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.50/1.78  thf('24', plain,
% 1.50/1.78      (![X0 : $i, X1 : $i]:
% 1.50/1.78         ((k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 1.50/1.78           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.50/1.78      inference('sup+', [status(thm)], ['22', '23'])).
% 1.50/1.78  thf('25', plain,
% 1.50/1.78      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.50/1.78      inference('sup+', [status(thm)], ['20', '21'])).
% 1.50/1.78  thf('26', plain,
% 1.50/1.78      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.50/1.78      inference('demod', [status(thm)], ['24', '25'])).
% 1.50/1.78  thf('27', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.50/1.78      inference('cnf', [status(esa)], [t3_boole])).
% 1.50/1.78  thf('28', plain,
% 1.50/1.78      (![X0 : $i, X1 : $i]:
% 1.50/1.78         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.50/1.78      inference('demod', [status(thm)], ['19', '26', '27'])).
% 1.50/1.78  thf('29', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.50/1.78      inference('sup+', [status(thm)], ['16', '28'])).
% 1.50/1.78  thf('30', plain,
% 1.50/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.78         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X0)))
% 1.50/1.78           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 1.50/1.78      inference('demod', [status(thm)], ['15', '29'])).
% 1.50/1.78  thf('31', plain,
% 1.50/1.78      (![X0 : $i, X1 : $i]:
% 1.50/1.78         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.50/1.78      inference('demod', [status(thm)], ['7', '30'])).
% 1.50/1.78  thf('32', plain,
% 1.50/1.78      (![X8 : $i, X9 : $i]:
% 1.50/1.78         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.50/1.78           = (k3_xboole_0 @ X8 @ X9))),
% 1.50/1.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.50/1.78  thf('33', plain,
% 1.50/1.78      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.50/1.78         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 1.50/1.78           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 1.50/1.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.50/1.78  thf('34', plain,
% 1.50/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.78         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.50/1.78           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 1.50/1.78      inference('sup+', [status(thm)], ['32', '33'])).
% 1.50/1.78  thf('35', plain,
% 1.50/1.78      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.50/1.78         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 1.50/1.78           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 1.50/1.78      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.50/1.78  thf('36', plain,
% 1.50/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.78         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2))
% 1.50/1.78           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 1.50/1.78      inference('demod', [status(thm)], ['34', '35'])).
% 1.50/1.78  thf('37', plain,
% 1.50/1.78      (![X0 : $i, X1 : $i]:
% 1.50/1.78         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.50/1.78      inference('sup+', [status(thm)], ['31', '36'])).
% 1.50/1.78  thf('38', plain,
% 1.50/1.78      (![X8 : $i, X9 : $i]:
% 1.50/1.78         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.50/1.78           = (k3_xboole_0 @ X8 @ X9))),
% 1.50/1.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.61/1.78  thf('39', plain,
% 1.61/1.78      (![X8 : $i, X9 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.61/1.78           = (k3_xboole_0 @ X8 @ X9))),
% 1.61/1.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.61/1.78  thf('40', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.61/1.78           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.61/1.78      inference('sup+', [status(thm)], ['38', '39'])).
% 1.61/1.78  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.61/1.78      inference('demod', [status(thm)], ['3', '4'])).
% 1.61/1.78  thf('42', plain,
% 1.61/1.78      (![X8 : $i, X9 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.61/1.78           = (k3_xboole_0 @ X8 @ X9))),
% 1.61/1.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.61/1.78  thf('43', plain,
% 1.61/1.78      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.61/1.78      inference('sup+', [status(thm)], ['41', '42'])).
% 1.61/1.78  thf('44', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.61/1.78      inference('cnf', [status(esa)], [t3_boole])).
% 1.61/1.78  thf('45', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.61/1.78      inference('demod', [status(thm)], ['43', '44'])).
% 1.61/1.78  thf('46', plain,
% 1.61/1.78      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.61/1.78         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 1.61/1.78           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 1.61/1.78      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.61/1.78  thf('47', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.61/1.78           = (k4_xboole_0 @ X0 @ X1))),
% 1.61/1.78      inference('sup+', [status(thm)], ['45', '46'])).
% 1.61/1.78  thf('48', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.61/1.78           = (k4_xboole_0 @ X1 @ X0))),
% 1.61/1.78      inference('demod', [status(thm)], ['40', '47'])).
% 1.61/1.78  thf('49', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 1.61/1.78           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.61/1.78      inference('sup+', [status(thm)], ['37', '48'])).
% 1.61/1.78  thf('50', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.61/1.78      inference('cnf', [status(esa)], [t3_boole])).
% 1.61/1.78  thf('51', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.61/1.78      inference('demod', [status(thm)], ['49', '50'])).
% 1.61/1.78  thf('52', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.61/1.78      inference('demod', [status(thm)], ['49', '50'])).
% 1.61/1.78  thf('53', plain,
% 1.61/1.78      (![X8 : $i, X9 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.61/1.78           = (k3_xboole_0 @ X8 @ X9))),
% 1.61/1.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.61/1.78  thf('54', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf('55', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.61/1.78      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.61/1.78  thf('56', plain,
% 1.61/1.78      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['54', '55'])).
% 1.61/1.78  thf('57', plain,
% 1.61/1.78      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 1.61/1.78           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 1.61/1.78              (k3_xboole_0 @ X13 @ X15)))),
% 1.61/1.78      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.61/1.78  thf('58', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ sk_A @ 
% 1.61/1.78           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 1.61/1.78           = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ k1_xboole_0))),
% 1.61/1.78      inference('sup+', [status(thm)], ['56', '57'])).
% 1.61/1.78  thf('59', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.61/1.78      inference('sup+', [status(thm)], ['16', '28'])).
% 1.61/1.78  thf('60', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ sk_A @ 
% 1.61/1.78           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 1.61/1.78           = (k4_xboole_0 @ sk_A @ X0))),
% 1.61/1.78      inference('demod', [status(thm)], ['58', '59'])).
% 1.61/1.78  thf('61', plain,
% 1.61/1.78      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 1.61/1.78         = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.61/1.78      inference('sup+', [status(thm)], ['53', '60'])).
% 1.61/1.78  thf('62', plain,
% 1.61/1.78      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 1.61/1.78           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 1.61/1.78              (k3_xboole_0 @ X13 @ X15)))),
% 1.61/1.78      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.61/1.78  thf('63', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ sk_A @ 
% 1.61/1.78           (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ X0))
% 1.61/1.78           = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 1.61/1.78              (k3_xboole_0 @ sk_A @ X0)))),
% 1.61/1.78      inference('sup+', [status(thm)], ['61', '62'])).
% 1.61/1.78  thf('64', plain,
% 1.61/1.78      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.61/1.78         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 1.61/1.78           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 1.61/1.78      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.61/1.78  thf('65', plain,
% 1.61/1.78      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 1.61/1.78           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 1.61/1.78              (k3_xboole_0 @ X13 @ X15)))),
% 1.61/1.78      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.61/1.78  thf('66', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ sk_A @ 
% 1.61/1.78           (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ X0)))
% 1.61/1.78           = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 1.61/1.78      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.61/1.78  thf('67', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 1.61/1.78           = (k4_xboole_0 @ sk_A @ 
% 1.61/1.78              (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))))),
% 1.61/1.78      inference('sup+', [status(thm)], ['52', '66'])).
% 1.61/1.78  thf('68', plain,
% 1.61/1.78      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 1.61/1.78         = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.61/1.78      inference('sup+', [status(thm)], ['53', '60'])).
% 1.61/1.78  thf('69', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ sk_A @ sk_B)
% 1.61/1.78           = (k4_xboole_0 @ sk_A @ 
% 1.61/1.78              (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))))),
% 1.61/1.78      inference('demod', [status(thm)], ['67', '68'])).
% 1.61/1.78  thf('70', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.61/1.78           = (k4_xboole_0 @ X0 @ X1))),
% 1.61/1.78      inference('sup+', [status(thm)], ['45', '46'])).
% 1.61/1.78  thf('71', plain,
% 1.61/1.78      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 1.61/1.78           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 1.61/1.78              (k3_xboole_0 @ X13 @ X15)))),
% 1.61/1.78      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.61/1.78  thf('72', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 1.61/1.78           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.61/1.78      inference('sup+', [status(thm)], ['70', '71'])).
% 1.61/1.78  thf('73', plain,
% 1.61/1.78      (((k4_xboole_0 @ sk_A @ sk_B)
% 1.61/1.78         = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 1.61/1.78            (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.61/1.78      inference('sup+', [status(thm)], ['69', '72'])).
% 1.61/1.78  thf('74', plain,
% 1.61/1.78      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 1.61/1.78           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 1.61/1.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.61/1.78  thf('75', plain,
% 1.61/1.78      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 1.61/1.78      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.61/1.78  thf('76', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.78         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0)),
% 1.61/1.78      inference('sup+', [status(thm)], ['74', '75'])).
% 1.61/1.78  thf('77', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 1.61/1.78          (k4_xboole_0 @ sk_A @ sk_C))),
% 1.61/1.78      inference('sup+', [status(thm)], ['73', '76'])).
% 1.61/1.78  thf('78', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 1.61/1.78      inference('sup+', [status(thm)], ['51', '77'])).
% 1.61/1.78  thf('79', plain, ($false), inference('demod', [status(thm)], ['0', '78'])).
% 1.61/1.78  
% 1.61/1.78  % SZS output end Refutation
% 1.61/1.78  
% 1.61/1.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
