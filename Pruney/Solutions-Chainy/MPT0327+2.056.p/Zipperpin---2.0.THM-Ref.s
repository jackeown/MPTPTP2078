%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9alqmuvmK9

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:57 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 699 expanded)
%              Number of leaves         :   23 ( 224 expanded)
%              Depth                    :   18
%              Number of atoms          : 1017 (5205 expanded)
%              Number of equality atoms :  113 ( 604 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['9','21'])).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('23',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('24',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X40 ) @ X42 )
      | ~ ( r2_hidden @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('25',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('30',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','16'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['22','38'])).

thf('40',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('55',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('61',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('65',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('66',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('67',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('70',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('79',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('82',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['80','89'])).

thf('91',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['80','89'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('95',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('96',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['93','94','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['90','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['77','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['68','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['59','107'])).

thf('109',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['56','108'])).

thf('110',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['55','109'])).

thf('111',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('113',plain,(
    ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['110','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9alqmuvmK9
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:25:48 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.58/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.82  % Solved by: fo/fo7.sh
% 0.58/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.82  % done 1029 iterations in 0.371s
% 0.58/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.82  % SZS output start Refutation
% 0.58/0.82  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.82  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.58/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.82  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.82  thf(t48_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.58/0.82  thf('0', plain,
% 0.58/0.82      (![X15 : $i, X16 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.58/0.82           = (k3_xboole_0 @ X15 @ X16))),
% 0.58/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.82  thf('1', plain,
% 0.58/0.82      (![X15 : $i, X16 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.58/0.82           = (k3_xboole_0 @ X15 @ X16))),
% 0.58/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.82  thf(t36_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.58/0.82  thf('2', plain,
% 0.58/0.82      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.58/0.82      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.58/0.82  thf(l32_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.82  thf('3', plain,
% 0.58/0.82      (![X3 : $i, X5 : $i]:
% 0.58/0.82         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.58/0.82      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.82  thf('4', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.82  thf('5', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['1', '4'])).
% 0.58/0.82  thf(t49_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.58/0.82       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.58/0.82  thf('6', plain,
% 0.58/0.82      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.82         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.58/0.82           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 0.58/0.82      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.58/0.82  thf(t100_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.58/0.82  thf('7', plain,
% 0.58/0.82      (![X6 : $i, X7 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X6 @ X7)
% 0.58/0.82           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.82  thf('8', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.58/0.82           = (k5_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['6', '7'])).
% 0.58/0.82  thf('9', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.58/0.82           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['5', '8'])).
% 0.58/0.82  thf(t3_boole, axiom,
% 0.58/0.82    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.58/0.82  thf('10', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.58/0.82      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.82  thf('11', plain,
% 0.58/0.82      (![X15 : $i, X16 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.58/0.82           = (k3_xboole_0 @ X15 @ X16))),
% 0.58/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.82  thf('12', plain,
% 0.58/0.82      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['10', '11'])).
% 0.58/0.82  thf(d10_xboole_0, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.82  thf('13', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.58/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.82  thf('14', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.58/0.82      inference('simplify', [status(thm)], ['13'])).
% 0.58/0.82  thf('15', plain,
% 0.58/0.82      (![X3 : $i, X5 : $i]:
% 0.58/0.82         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.58/0.82      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.82  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.82  thf('17', plain,
% 0.58/0.82      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['12', '16'])).
% 0.58/0.82  thf('18', plain,
% 0.58/0.82      (![X6 : $i, X7 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X6 @ X7)
% 0.58/0.82           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.82  thf('19', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['17', '18'])).
% 0.58/0.82  thf('20', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.58/0.82      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.82  thf('21', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['19', '20'])).
% 0.58/0.82  thf('22', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['9', '21'])).
% 0.58/0.82  thf(t140_zfmisc_1, conjecture,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( r2_hidden @ A @ B ) =>
% 0.58/0.82       ( ( k2_xboole_0 @
% 0.58/0.82           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.58/0.82         ( B ) ) ))).
% 0.58/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.82    (~( ![A:$i,B:$i]:
% 0.58/0.82        ( ( r2_hidden @ A @ B ) =>
% 0.58/0.82          ( ( k2_xboole_0 @
% 0.58/0.82              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.58/0.82            ( B ) ) ) )),
% 0.58/0.82    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.58/0.82  thf('23', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(l1_zfmisc_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.58/0.82  thf('24', plain,
% 0.58/0.82      (![X40 : $i, X42 : $i]:
% 0.58/0.82         ((r1_tarski @ (k1_tarski @ X40) @ X42) | ~ (r2_hidden @ X40 @ X42))),
% 0.58/0.82      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.58/0.82  thf('25', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.58/0.82      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.82  thf(t28_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.58/0.82  thf('26', plain,
% 0.58/0.82      (![X8 : $i, X9 : $i]:
% 0.58/0.82         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.58/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.82  thf('27', plain,
% 0.58/0.82      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.82  thf('28', plain,
% 0.58/0.82      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.82         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.58/0.82           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 0.58/0.82      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.58/0.82  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.82  thf('30', plain,
% 0.58/0.82      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.82         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.58/0.82           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 0.58/0.82      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.58/0.82  thf('31', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k3_xboole_0 @ X1 @ k1_xboole_0)
% 0.58/0.82           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['29', '30'])).
% 0.58/0.82  thf('32', plain,
% 0.58/0.82      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['12', '16'])).
% 0.58/0.82  thf('33', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['31', '32'])).
% 0.58/0.82  thf('34', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         ((k1_xboole_0)
% 0.58/0.82           = (k4_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 0.58/0.82              (k4_xboole_0 @ X1 @ X0)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['28', '33'])).
% 0.58/0.82  thf('35', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((k1_xboole_0)
% 0.58/0.82           = (k4_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ 
% 0.58/0.82              (k4_xboole_0 @ sk_B @ X0)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['27', '34'])).
% 0.58/0.82  thf('36', plain,
% 0.58/0.82      (![X3 : $i, X4 : $i]:
% 0.58/0.82         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.58/0.82      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.82  thf('37', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.82          | (r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ 
% 0.58/0.82             (k4_xboole_0 @ sk_B @ X0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['35', '36'])).
% 0.58/0.82  thf('38', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ 
% 0.58/0.82          (k4_xboole_0 @ sk_B @ X0))),
% 0.58/0.82      inference('simplify', [status(thm)], ['37'])).
% 0.58/0.82  thf('39', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.58/0.82          (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 0.58/0.82      inference('sup+', [status(thm)], ['22', '38'])).
% 0.58/0.82  thf('40', plain,
% 0.58/0.82      ((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.58/0.82        (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['0', '39'])).
% 0.58/0.82  thf('41', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['31', '32'])).
% 0.58/0.82  thf('42', plain,
% 0.58/0.82      (![X3 : $i, X4 : $i]:
% 0.58/0.82         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.58/0.82      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.82  thf('43', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         (((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.82          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['41', '42'])).
% 0.58/0.82  thf('44', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.58/0.82      inference('simplify', [status(thm)], ['43'])).
% 0.58/0.82  thf('45', plain,
% 0.58/0.82      (![X0 : $i, X2 : $i]:
% 0.58/0.82         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.58/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.82  thf('46', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.58/0.82          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['44', '45'])).
% 0.58/0.82  thf('47', plain,
% 0.58/0.82      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['40', '46'])).
% 0.58/0.82  thf('48', plain,
% 0.58/0.82      (![X6 : $i, X7 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X6 @ X7)
% 0.58/0.82           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.82  thf('49', plain,
% 0.58/0.82      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.58/0.82         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['47', '48'])).
% 0.58/0.82  thf('50', plain,
% 0.58/0.82      (![X15 : $i, X16 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.58/0.82           = (k3_xboole_0 @ X15 @ X16))),
% 0.58/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.82  thf('51', plain,
% 0.58/0.82      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.58/0.82         = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['49', '50'])).
% 0.58/0.82  thf('52', plain,
% 0.58/0.82      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['40', '46'])).
% 0.58/0.82  thf('53', plain,
% 0.58/0.82      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.58/0.82         = (k1_tarski @ sk_A))),
% 0.58/0.82      inference('demod', [status(thm)], ['51', '52'])).
% 0.58/0.82  thf(t39_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.82  thf('54', plain,
% 0.58/0.82      (![X12 : $i, X13 : $i]:
% 0.58/0.82         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.58/0.82           = (k2_xboole_0 @ X12 @ X13))),
% 0.58/0.82      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.58/0.82  thf('55', plain,
% 0.58/0.82      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.82         (k1_tarski @ sk_A))
% 0.58/0.82         = (k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B))),
% 0.58/0.82      inference('sup+', [status(thm)], ['53', '54'])).
% 0.58/0.82  thf('56', plain,
% 0.58/0.82      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.58/0.82         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['47', '48'])).
% 0.58/0.82  thf('57', plain,
% 0.58/0.82      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.58/0.82      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.58/0.82  thf('58', plain,
% 0.58/0.82      (![X8 : $i, X9 : $i]:
% 0.58/0.82         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.58/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.82  thf('59', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.58/0.82           = (k4_xboole_0 @ X0 @ X1))),
% 0.58/0.82      inference('sup-', [status(thm)], ['57', '58'])).
% 0.58/0.82  thf('60', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['31', '32'])).
% 0.58/0.82  thf('61', plain,
% 0.58/0.82      (![X15 : $i, X16 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.58/0.82           = (k3_xboole_0 @ X15 @ X16))),
% 0.58/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.82  thf('62', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 0.58/0.82           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['60', '61'])).
% 0.58/0.82  thf('63', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.58/0.82      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.82  thf('64', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k3_xboole_0 @ X1 @ X0)
% 0.58/0.82           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['62', '63'])).
% 0.58/0.82  thf(t94_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( k2_xboole_0 @ A @ B ) =
% 0.58/0.82       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.58/0.82  thf('65', plain,
% 0.58/0.82      (![X23 : $i, X24 : $i]:
% 0.58/0.82         ((k2_xboole_0 @ X23 @ X24)
% 0.58/0.82           = (k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ 
% 0.58/0.82              (k3_xboole_0 @ X23 @ X24)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.58/0.82  thf(t91_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.58/0.82       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.58/0.82  thf('66', plain,
% 0.58/0.82      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.58/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.58/0.82           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.58/0.82  thf('67', plain,
% 0.58/0.82      (![X23 : $i, X24 : $i]:
% 0.58/0.82         ((k2_xboole_0 @ X23 @ X24)
% 0.58/0.82           = (k5_xboole_0 @ X23 @ 
% 0.58/0.82              (k5_xboole_0 @ X24 @ (k3_xboole_0 @ X23 @ X24))))),
% 0.58/0.82      inference('demod', [status(thm)], ['65', '66'])).
% 0.58/0.82  thf('68', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.58/0.82           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.58/0.82              (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.58/0.82      inference('sup+', [status(thm)], ['64', '67'])).
% 0.58/0.82  thf('69', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.58/0.82      inference('simplify', [status(thm)], ['13'])).
% 0.58/0.82  thf('70', plain,
% 0.58/0.82      (![X8 : $i, X9 : $i]:
% 0.58/0.82         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.58/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.82  thf('71', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['69', '70'])).
% 0.58/0.82  thf('72', plain,
% 0.58/0.82      (![X6 : $i, X7 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X6 @ X7)
% 0.58/0.82           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.82  thf('73', plain,
% 0.58/0.82      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['71', '72'])).
% 0.58/0.82  thf('74', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.82  thf('75', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['73', '74'])).
% 0.58/0.82  thf('76', plain,
% 0.58/0.82      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.58/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.58/0.82           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.58/0.82  thf('77', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k1_xboole_0)
% 0.58/0.82           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.58/0.82      inference('sup+', [status(thm)], ['75', '76'])).
% 0.58/0.82  thf('78', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['73', '74'])).
% 0.58/0.82  thf('79', plain,
% 0.58/0.82      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.58/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.58/0.82           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.58/0.82  thf('80', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.58/0.82           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['78', '79'])).
% 0.58/0.82  thf('81', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.82  thf('82', plain,
% 0.58/0.82      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.58/0.82      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.58/0.82  thf('83', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.82      inference('sup+', [status(thm)], ['81', '82'])).
% 0.58/0.82  thf('84', plain,
% 0.58/0.82      (![X8 : $i, X9 : $i]:
% 0.58/0.82         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.58/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.82  thf('85', plain,
% 0.58/0.82      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['83', '84'])).
% 0.58/0.82  thf('86', plain,
% 0.58/0.82      (![X23 : $i, X24 : $i]:
% 0.58/0.82         ((k2_xboole_0 @ X23 @ X24)
% 0.58/0.82           = (k5_xboole_0 @ X23 @ 
% 0.58/0.82              (k5_xboole_0 @ X24 @ (k3_xboole_0 @ X23 @ X24))))),
% 0.58/0.82      inference('demod', [status(thm)], ['65', '66'])).
% 0.58/0.82  thf('87', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.58/0.82           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['85', '86'])).
% 0.58/0.82  thf('88', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['19', '20'])).
% 0.58/0.82  thf('89', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['87', '88'])).
% 0.58/0.82  thf('90', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.58/0.82           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['80', '89'])).
% 0.58/0.82  thf('91', plain,
% 0.58/0.82      (![X23 : $i, X24 : $i]:
% 0.58/0.82         ((k2_xboole_0 @ X23 @ X24)
% 0.58/0.82           = (k5_xboole_0 @ X23 @ 
% 0.58/0.82              (k5_xboole_0 @ X24 @ (k3_xboole_0 @ X23 @ X24))))),
% 0.58/0.82      inference('demod', [status(thm)], ['65', '66'])).
% 0.58/0.82  thf('92', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.58/0.82           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['80', '89'])).
% 0.58/0.82  thf('93', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0))
% 0.58/0.82           = (k2_xboole_0 @ X0 @ X0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['91', '92'])).
% 0.58/0.82  thf('94', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['69', '70'])).
% 0.58/0.82  thf('95', plain,
% 0.58/0.82      (![X6 : $i, X7 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X6 @ X7)
% 0.58/0.82           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.82  thf('96', plain,
% 0.58/0.82      (![X23 : $i, X24 : $i]:
% 0.58/0.82         ((k2_xboole_0 @ X23 @ X24)
% 0.58/0.82           = (k5_xboole_0 @ X23 @ 
% 0.58/0.82              (k5_xboole_0 @ X24 @ (k3_xboole_0 @ X23 @ X24))))),
% 0.58/0.82      inference('demod', [status(thm)], ['65', '66'])).
% 0.58/0.82  thf('97', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((k2_xboole_0 @ X0 @ X0)
% 0.58/0.82           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['95', '96'])).
% 0.58/0.82  thf('98', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.82  thf('99', plain,
% 0.58/0.82      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['97', '98'])).
% 0.58/0.82  thf('100', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['19', '20'])).
% 0.58/0.82  thf('101', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['99', '100'])).
% 0.58/0.82  thf('102', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['93', '94', '101'])).
% 0.58/0.82  thf('103', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['90', '102'])).
% 0.58/0.82  thf('104', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.58/0.82           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['77', '103'])).
% 0.58/0.82  thf('105', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['19', '20'])).
% 0.58/0.82  thf('106', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.58/0.82      inference('demod', [status(thm)], ['104', '105'])).
% 0.58/0.82  thf('107', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['68', '106'])).
% 0.58/0.82  thf('108', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.58/0.82      inference('sup+', [status(thm)], ['59', '107'])).
% 0.58/0.82  thf('109', plain,
% 0.58/0.82      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 0.58/0.82         = (sk_B))),
% 0.58/0.82      inference('sup+', [status(thm)], ['56', '108'])).
% 0.58/0.82  thf('110', plain,
% 0.58/0.82      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.82         (k1_tarski @ sk_A)) = (sk_B))),
% 0.58/0.82      inference('demod', [status(thm)], ['55', '109'])).
% 0.58/0.82  thf('111', plain,
% 0.58/0.82      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.82         (k1_tarski @ sk_A)) != (sk_B))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('112', plain,
% 0.58/0.82      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.58/0.82         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['47', '48'])).
% 0.58/0.82  thf('113', plain,
% 0.58/0.82      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.82         (k1_tarski @ sk_A)) != (sk_B))),
% 0.58/0.82      inference('demod', [status(thm)], ['111', '112'])).
% 0.58/0.82  thf('114', plain, ($false),
% 0.58/0.82      inference('simplify_reflect-', [status(thm)], ['110', '113'])).
% 0.58/0.82  
% 0.58/0.82  % SZS output end Refutation
% 0.58/0.82  
% 0.68/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
