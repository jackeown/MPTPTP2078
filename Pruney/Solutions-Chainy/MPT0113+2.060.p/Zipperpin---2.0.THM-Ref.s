%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sXeMbJ7p5I

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:36 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 735 expanded)
%              Number of leaves         :   23 ( 255 expanded)
%              Depth                    :   21
%              Number of atoms          :  996 (5409 expanded)
%              Number of equality atoms :  103 ( 570 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['2','5'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','30'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('39',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('53',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('56',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('57',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('65',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('84',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('85',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['54','91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','93'])).

thf('95',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['31','94'])).

thf('96',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('97',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','93'])).

thf('99',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('101',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('103',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('112',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['101','110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('114',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['112','119'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['11','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sXeMbJ7p5I
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.49/1.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.49/1.73  % Solved by: fo/fo7.sh
% 1.49/1.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.49/1.73  % done 3306 iterations in 1.273s
% 1.49/1.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.49/1.73  % SZS output start Refutation
% 1.49/1.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.49/1.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.49/1.73  thf(sk_A_type, type, sk_A: $i).
% 1.49/1.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.49/1.73  thf(sk_C_type, type, sk_C: $i).
% 1.49/1.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.49/1.73  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.49/1.73  thf(sk_B_type, type, sk_B: $i).
% 1.49/1.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.49/1.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.49/1.73  thf(t106_xboole_1, conjecture,
% 1.49/1.73    (![A:$i,B:$i,C:$i]:
% 1.49/1.73     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.49/1.73       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 1.49/1.73  thf(zf_stmt_0, negated_conjecture,
% 1.49/1.73    (~( ![A:$i,B:$i,C:$i]:
% 1.49/1.73        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.49/1.73          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 1.49/1.73    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 1.49/1.73  thf('0', plain,
% 1.49/1.73      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 1.49/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.73  thf('1', plain,
% 1.49/1.73      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 1.49/1.73      inference('split', [status(esa)], ['0'])).
% 1.49/1.73  thf(t79_xboole_1, axiom,
% 1.49/1.73    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.49/1.73  thf('2', plain,
% 1.49/1.73      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 1.49/1.73      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.49/1.73  thf('3', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.49/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.73  thf(t63_xboole_1, axiom,
% 1.49/1.73    (![A:$i,B:$i,C:$i]:
% 1.49/1.73     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.49/1.73       ( r1_xboole_0 @ A @ C ) ))).
% 1.49/1.73  thf('4', plain,
% 1.49/1.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.49/1.73         (~ (r1_tarski @ X15 @ X16)
% 1.49/1.73          | ~ (r1_xboole_0 @ X16 @ X17)
% 1.49/1.73          | (r1_xboole_0 @ X15 @ X17))),
% 1.49/1.73      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.49/1.73  thf('5', plain,
% 1.49/1.73      (![X0 : $i]:
% 1.49/1.73         ((r1_xboole_0 @ sk_A @ X0)
% 1.49/1.73          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))),
% 1.49/1.73      inference('sup-', [status(thm)], ['3', '4'])).
% 1.49/1.73  thf('6', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 1.49/1.73      inference('sup-', [status(thm)], ['2', '5'])).
% 1.49/1.73  thf('7', plain,
% 1.49/1.73      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 1.49/1.73      inference('split', [status(esa)], ['0'])).
% 1.49/1.73  thf('8', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 1.49/1.73      inference('sup-', [status(thm)], ['6', '7'])).
% 1.49/1.73  thf('9', plain,
% 1.49/1.73      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 1.49/1.73      inference('split', [status(esa)], ['0'])).
% 1.49/1.73  thf('10', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 1.49/1.73      inference('sat_resolution*', [status(thm)], ['8', '9'])).
% 1.49/1.73  thf('11', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 1.49/1.73      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 1.49/1.73  thf('12', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.49/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.73  thf(t12_xboole_1, axiom,
% 1.49/1.73    (![A:$i,B:$i]:
% 1.49/1.73     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.49/1.73  thf('13', plain,
% 1.49/1.73      (![X5 : $i, X6 : $i]:
% 1.49/1.73         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.49/1.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.49/1.73  thf('14', plain,
% 1.49/1.73      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 1.49/1.73         = (k4_xboole_0 @ sk_B @ sk_C))),
% 1.49/1.73      inference('sup-', [status(thm)], ['12', '13'])).
% 1.49/1.73  thf(t95_xboole_1, axiom,
% 1.49/1.73    (![A:$i,B:$i]:
% 1.49/1.73     ( ( k3_xboole_0 @ A @ B ) =
% 1.49/1.73       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.49/1.73  thf('15', plain,
% 1.49/1.73      (![X24 : $i, X25 : $i]:
% 1.49/1.73         ((k3_xboole_0 @ X24 @ X25)
% 1.49/1.73           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 1.49/1.73              (k2_xboole_0 @ X24 @ X25)))),
% 1.49/1.73      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.49/1.73  thf(t91_xboole_1, axiom,
% 1.49/1.73    (![A:$i,B:$i,C:$i]:
% 1.49/1.73     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.49/1.73       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.49/1.73  thf('16', plain,
% 1.49/1.73      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.49/1.73         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 1.49/1.73           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 1.49/1.73      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.49/1.73  thf('17', plain,
% 1.49/1.73      (![X24 : $i, X25 : $i]:
% 1.49/1.73         ((k3_xboole_0 @ X24 @ X25)
% 1.49/1.73           = (k5_xboole_0 @ X24 @ 
% 1.49/1.73              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 1.49/1.73      inference('demod', [status(thm)], ['15', '16'])).
% 1.49/1.73  thf('18', plain,
% 1.49/1.73      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 1.49/1.73         = (k5_xboole_0 @ sk_A @ 
% 1.49/1.73            (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ 
% 1.49/1.73             (k4_xboole_0 @ sk_B @ sk_C))))),
% 1.49/1.73      inference('sup+', [status(thm)], ['14', '17'])).
% 1.49/1.73  thf(t92_xboole_1, axiom,
% 1.49/1.73    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.49/1.73  thf('19', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 1.49/1.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.49/1.73  thf(t5_boole, axiom,
% 1.49/1.73    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.49/1.73  thf('20', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.49/1.73      inference('cnf', [status(esa)], [t5_boole])).
% 1.49/1.73  thf('21', plain,
% 1.49/1.73      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 1.49/1.73      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.49/1.73  thf(t100_xboole_1, axiom,
% 1.49/1.73    (![A:$i,B:$i]:
% 1.49/1.73     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.49/1.73  thf('22', plain,
% 1.49/1.73      (![X3 : $i, X4 : $i]:
% 1.49/1.73         ((k4_xboole_0 @ X3 @ X4)
% 1.49/1.73           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.49/1.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.49/1.73  thf('23', plain,
% 1.49/1.73      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 1.49/1.73         = (k5_xboole_0 @ sk_A @ sk_A))),
% 1.49/1.73      inference('sup+', [status(thm)], ['21', '22'])).
% 1.49/1.73  thf('24', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 1.49/1.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.49/1.73  thf('25', plain,
% 1.49/1.73      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 1.49/1.73      inference('demod', [status(thm)], ['23', '24'])).
% 1.49/1.73  thf('26', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 1.49/1.73      inference('sup-', [status(thm)], ['2', '5'])).
% 1.49/1.73  thf(d7_xboole_0, axiom,
% 1.49/1.73    (![A:$i,B:$i]:
% 1.49/1.73     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.49/1.73       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.49/1.73  thf('27', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.49/1.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.49/1.73  thf('28', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 1.49/1.73      inference('sup-', [status(thm)], ['26', '27'])).
% 1.49/1.73  thf(t52_xboole_1, axiom,
% 1.49/1.73    (![A:$i,B:$i,C:$i]:
% 1.49/1.73     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.49/1.73       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.49/1.73  thf('29', plain,
% 1.49/1.73      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.49/1.73         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 1.49/1.73           = (k2_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ 
% 1.49/1.73              (k3_xboole_0 @ X11 @ X13)))),
% 1.49/1.73      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.49/1.73  thf('30', plain,
% 1.49/1.73      (![X0 : $i]:
% 1.49/1.73         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 1.49/1.73           = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ k1_xboole_0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['28', '29'])).
% 1.49/1.73  thf('31', plain,
% 1.49/1.73      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)
% 1.49/1.73         = (k1_xboole_0))),
% 1.49/1.73      inference('demod', [status(thm)], ['25', '30'])).
% 1.49/1.73  thf(t39_xboole_1, axiom,
% 1.49/1.73    (![A:$i,B:$i]:
% 1.49/1.73     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.49/1.73  thf('32', plain,
% 1.49/1.73      (![X9 : $i, X10 : $i]:
% 1.49/1.73         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 1.49/1.73           = (k2_xboole_0 @ X9 @ X10))),
% 1.49/1.73      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.49/1.73  thf(t36_xboole_1, axiom,
% 1.49/1.73    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.49/1.73  thf('33', plain,
% 1.49/1.73      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 1.49/1.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.49/1.73  thf('34', plain,
% 1.49/1.73      (![X5 : $i, X6 : $i]:
% 1.49/1.73         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.49/1.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.49/1.73  thf('35', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.49/1.73      inference('sup-', [status(thm)], ['33', '34'])).
% 1.49/1.73  thf('36', plain,
% 1.49/1.73      (![X24 : $i, X25 : $i]:
% 1.49/1.73         ((k3_xboole_0 @ X24 @ X25)
% 1.49/1.73           = (k5_xboole_0 @ X24 @ 
% 1.49/1.73              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 1.49/1.73      inference('demod', [status(thm)], ['15', '16'])).
% 1.49/1.73  thf('37', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.49/1.73           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0)))),
% 1.49/1.73      inference('sup+', [status(thm)], ['35', '36'])).
% 1.49/1.73  thf('38', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 1.49/1.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.49/1.73  thf('39', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.49/1.73      inference('cnf', [status(esa)], [t5_boole])).
% 1.49/1.73  thf('40', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.49/1.73           = (k4_xboole_0 @ X0 @ X1))),
% 1.49/1.73      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.49/1.73  thf('41', plain,
% 1.49/1.73      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 1.49/1.73      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.49/1.73  thf('42', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.49/1.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.49/1.73  thf('43', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.49/1.73      inference('sup-', [status(thm)], ['41', '42'])).
% 1.49/1.73  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['40', '43'])).
% 1.49/1.73  thf('45', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.49/1.73      inference('sup-', [status(thm)], ['33', '34'])).
% 1.49/1.73  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['44', '45'])).
% 1.49/1.73  thf('47', plain,
% 1.49/1.73      (![X0 : $i]:
% 1.49/1.73         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['32', '46'])).
% 1.49/1.73  thf('48', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['44', '45'])).
% 1.49/1.73  thf('49', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.49/1.73      inference('demod', [status(thm)], ['47', '48'])).
% 1.49/1.73  thf('50', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.49/1.73      inference('sup-', [status(thm)], ['41', '42'])).
% 1.49/1.73  thf('51', plain,
% 1.49/1.73      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['49', '50'])).
% 1.49/1.73  thf('52', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.49/1.73      inference('demod', [status(thm)], ['47', '48'])).
% 1.49/1.73  thf('53', plain,
% 1.49/1.73      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.49/1.73         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 1.49/1.73           = (k2_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ 
% 1.49/1.73              (k3_xboole_0 @ X11 @ X13)))),
% 1.49/1.73      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.49/1.73  thf('54', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 1.49/1.73           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.49/1.73      inference('sup+', [status(thm)], ['52', '53'])).
% 1.49/1.73  thf('55', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 1.49/1.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.49/1.73  thf('56', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 1.49/1.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.49/1.73  thf('57', plain,
% 1.49/1.73      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.49/1.73         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 1.49/1.73           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 1.49/1.73      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.49/1.73  thf('58', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.49/1.73           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.49/1.73      inference('sup+', [status(thm)], ['56', '57'])).
% 1.49/1.73  thf('59', plain,
% 1.49/1.73      (![X0 : $i]:
% 1.49/1.73         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['55', '58'])).
% 1.49/1.73  thf('60', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.49/1.73      inference('cnf', [status(esa)], [t5_boole])).
% 1.49/1.73  thf('61', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.49/1.73      inference('demod', [status(thm)], ['59', '60'])).
% 1.49/1.73  thf('62', plain,
% 1.49/1.73      (![X3 : $i, X4 : $i]:
% 1.49/1.73         ((k4_xboole_0 @ X3 @ X4)
% 1.49/1.73           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.49/1.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.49/1.73  thf('63', plain,
% 1.49/1.73      (![X0 : $i]:
% 1.49/1.73         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['61', '62'])).
% 1.49/1.73  thf('64', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.49/1.73      inference('sup-', [status(thm)], ['41', '42'])).
% 1.49/1.73  thf('65', plain,
% 1.49/1.73      (![X3 : $i, X4 : $i]:
% 1.49/1.73         ((k4_xboole_0 @ X3 @ X4)
% 1.49/1.73           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.49/1.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.49/1.73  thf('66', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.49/1.73           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['64', '65'])).
% 1.49/1.73  thf('67', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.49/1.73      inference('cnf', [status(esa)], [t5_boole])).
% 1.49/1.73  thf('68', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.49/1.73           = (k4_xboole_0 @ X1 @ X0))),
% 1.49/1.73      inference('demod', [status(thm)], ['66', '67'])).
% 1.49/1.73  thf('69', plain,
% 1.49/1.73      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 1.49/1.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.49/1.73  thf('70', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['68', '69'])).
% 1.49/1.73  thf('71', plain,
% 1.49/1.73      (![X5 : $i, X6 : $i]:
% 1.49/1.73         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.49/1.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.49/1.73  thf('72', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.49/1.73           = (k4_xboole_0 @ X1 @ X0))),
% 1.49/1.73      inference('sup-', [status(thm)], ['70', '71'])).
% 1.49/1.73  thf('73', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.49/1.73           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.49/1.73      inference('sup+', [status(thm)], ['56', '57'])).
% 1.49/1.73  thf('74', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.49/1.73      inference('demod', [status(thm)], ['59', '60'])).
% 1.49/1.73  thf('75', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.49/1.73      inference('demod', [status(thm)], ['73', '74'])).
% 1.49/1.73  thf('76', plain,
% 1.49/1.73      (![X24 : $i, X25 : $i]:
% 1.49/1.73         ((k3_xboole_0 @ X24 @ X25)
% 1.49/1.73           = (k5_xboole_0 @ X24 @ 
% 1.49/1.73              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 1.49/1.73      inference('demod', [status(thm)], ['15', '16'])).
% 1.49/1.73  thf('77', plain,
% 1.49/1.73      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['75', '76'])).
% 1.49/1.73  thf('78', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.49/1.73           = (k4_xboole_0 @ X1 @ X0))),
% 1.49/1.73      inference('demod', [status(thm)], ['72', '77'])).
% 1.49/1.73  thf('79', plain,
% 1.49/1.73      (![X3 : $i, X4 : $i]:
% 1.49/1.73         ((k4_xboole_0 @ X3 @ X4)
% 1.49/1.73           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.49/1.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.49/1.73  thf('80', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.49/1.73           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.49/1.73      inference('sup+', [status(thm)], ['78', '79'])).
% 1.49/1.73  thf('81', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 1.49/1.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.49/1.73  thf('82', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.49/1.73           = (k1_xboole_0))),
% 1.49/1.73      inference('demod', [status(thm)], ['80', '81'])).
% 1.49/1.73  thf('83', plain,
% 1.49/1.73      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 1.49/1.73      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.49/1.73  thf('84', plain,
% 1.49/1.73      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 1.49/1.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.49/1.73  thf('85', plain,
% 1.49/1.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.49/1.73         (~ (r1_tarski @ X15 @ X16)
% 1.49/1.73          | ~ (r1_xboole_0 @ X16 @ X17)
% 1.49/1.73          | (r1_xboole_0 @ X15 @ X17))),
% 1.49/1.73      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.49/1.73  thf('86', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.49/1.73         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 1.49/1.73          | ~ (r1_xboole_0 @ X0 @ X2))),
% 1.49/1.73      inference('sup-', [status(thm)], ['84', '85'])).
% 1.49/1.73  thf('87', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.49/1.73         (r1_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0)),
% 1.49/1.73      inference('sup-', [status(thm)], ['83', '86'])).
% 1.49/1.73  thf('88', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.49/1.73      inference('sup+', [status(thm)], ['82', '87'])).
% 1.49/1.73  thf('89', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.49/1.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.49/1.73  thf('90', plain,
% 1.49/1.73      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.49/1.73      inference('sup-', [status(thm)], ['88', '89'])).
% 1.49/1.73  thf('91', plain,
% 1.49/1.73      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.49/1.73      inference('demod', [status(thm)], ['63', '90'])).
% 1.49/1.73  thf('92', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.49/1.73      inference('demod', [status(thm)], ['47', '48'])).
% 1.49/1.73  thf('93', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.49/1.73      inference('demod', [status(thm)], ['54', '91', '92'])).
% 1.49/1.73  thf('94', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['51', '93'])).
% 1.49/1.73  thf('95', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 1.49/1.73      inference('demod', [status(thm)], ['31', '94'])).
% 1.49/1.73  thf('96', plain,
% 1.49/1.73      (![X9 : $i, X10 : $i]:
% 1.49/1.73         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 1.49/1.73           = (k2_xboole_0 @ X9 @ X10))),
% 1.49/1.73      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.49/1.73  thf('97', plain,
% 1.49/1.73      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 1.49/1.73      inference('sup+', [status(thm)], ['95', '96'])).
% 1.49/1.73  thf('98', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['51', '93'])).
% 1.49/1.73  thf('99', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_A))),
% 1.49/1.73      inference('demod', [status(thm)], ['97', '98'])).
% 1.49/1.73  thf('100', plain,
% 1.49/1.73      (![X24 : $i, X25 : $i]:
% 1.49/1.73         ((k3_xboole_0 @ X24 @ X25)
% 1.49/1.73           = (k5_xboole_0 @ X24 @ 
% 1.49/1.73              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 1.49/1.73      inference('demod', [status(thm)], ['15', '16'])).
% 1.49/1.73  thf('101', plain,
% 1.49/1.73      (((k3_xboole_0 @ sk_B @ sk_A)
% 1.49/1.73         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 1.49/1.73      inference('sup+', [status(thm)], ['99', '100'])).
% 1.49/1.73  thf('102', plain,
% 1.49/1.73      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.49/1.73         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 1.49/1.73           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 1.49/1.73      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.49/1.73  thf('103', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 1.49/1.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.49/1.73  thf('104', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 1.49/1.73           = (k1_xboole_0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['102', '103'])).
% 1.49/1.73  thf('105', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.49/1.73      inference('demod', [status(thm)], ['73', '74'])).
% 1.49/1.73  thf('106', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 1.49/1.73           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['104', '105'])).
% 1.49/1.73  thf('107', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.49/1.73      inference('cnf', [status(esa)], [t5_boole])).
% 1.49/1.73  thf('108', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 1.49/1.73      inference('demod', [status(thm)], ['106', '107'])).
% 1.49/1.73  thf('109', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.49/1.73      inference('demod', [status(thm)], ['73', '74'])).
% 1.49/1.73  thf('110', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['108', '109'])).
% 1.49/1.73  thf('111', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.49/1.73      inference('demod', [status(thm)], ['73', '74'])).
% 1.49/1.73  thf('112', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 1.49/1.73      inference('demod', [status(thm)], ['101', '110', '111'])).
% 1.49/1.73  thf('113', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['40', '43'])).
% 1.49/1.73  thf('114', plain,
% 1.49/1.73      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.49/1.73         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 1.49/1.73           = (k2_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ 
% 1.49/1.73              (k3_xboole_0 @ X11 @ X13)))),
% 1.49/1.73      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.49/1.73  thf('115', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.49/1.73           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.49/1.73      inference('sup+', [status(thm)], ['113', '114'])).
% 1.49/1.73  thf('116', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.49/1.73      inference('sup+', [status(thm)], ['44', '45'])).
% 1.49/1.73  thf('117', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]:
% 1.49/1.73         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.49/1.73           = (k3_xboole_0 @ X1 @ X0))),
% 1.49/1.73      inference('demod', [status(thm)], ['115', '116'])).
% 1.49/1.73  thf('118', plain,
% 1.49/1.73      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 1.49/1.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.49/1.73  thf('119', plain,
% 1.49/1.73      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.49/1.73      inference('sup+', [status(thm)], ['117', '118'])).
% 1.49/1.73  thf('120', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.49/1.73      inference('sup+', [status(thm)], ['112', '119'])).
% 1.49/1.73  thf('121', plain, ($false), inference('demod', [status(thm)], ['11', '120'])).
% 1.49/1.73  
% 1.49/1.73  % SZS output end Refutation
% 1.49/1.73  
% 1.49/1.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
