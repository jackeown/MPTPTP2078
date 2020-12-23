%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Wj9dRDUeY9

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:54 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  111 (1115 expanded)
%              Number of leaves         :   22 ( 356 expanded)
%              Depth                    :   19
%              Number of atoms          :  818 (8215 expanded)
%              Number of equality atoms :   92 ( 982 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X31: $i,X33: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X31 ) @ X33 )
      | ~ ( r2_hidden @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
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

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
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

thf('8',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['11','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['19','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('34',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('36',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','42'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','49'])).

thf('51',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('52',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['10','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('60',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','67','68'])).

thf('70',plain,
    ( ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['53','69'])).

thf('71',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('74',plain,
    ( ( k1_tarski @ sk_A )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('76',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('82',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['76','77','78','79','82'])).

thf('84',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('86',plain,(
    ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['83','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Wj9dRDUeY9
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:26:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.50/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.67  % Solved by: fo/fo7.sh
% 0.50/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.67  % done 458 iterations in 0.217s
% 0.50/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.67  % SZS output start Refutation
% 0.50/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.50/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.50/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.67  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.50/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.67  thf(t140_zfmisc_1, conjecture,
% 0.50/0.67    (![A:$i,B:$i]:
% 0.50/0.67     ( ( r2_hidden @ A @ B ) =>
% 0.50/0.67       ( ( k2_xboole_0 @
% 0.50/0.67           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.50/0.67         ( B ) ) ))).
% 0.50/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.67    (~( ![A:$i,B:$i]:
% 0.50/0.67        ( ( r2_hidden @ A @ B ) =>
% 0.50/0.67          ( ( k2_xboole_0 @
% 0.50/0.67              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.50/0.67            ( B ) ) ) )),
% 0.50/0.67    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.50/0.67  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf(l1_zfmisc_1, axiom,
% 0.50/0.67    (![A:$i,B:$i]:
% 0.50/0.67     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.50/0.67  thf('1', plain,
% 0.50/0.67      (![X31 : $i, X33 : $i]:
% 0.50/0.67         ((r1_tarski @ (k1_tarski @ X31) @ X33) | ~ (r2_hidden @ X31 @ X33))),
% 0.50/0.67      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.50/0.67  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.50/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.50/0.67  thf(t28_xboole_1, axiom,
% 0.50/0.67    (![A:$i,B:$i]:
% 0.50/0.67     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.50/0.67  thf('3', plain,
% 0.50/0.67      (![X10 : $i, X11 : $i]:
% 0.50/0.67         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.50/0.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.67  thf('4', plain,
% 0.50/0.67      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.50/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.67  thf(commutativity_k3_xboole_0, axiom,
% 0.50/0.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.50/0.67  thf('5', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.67  thf('6', plain,
% 0.50/0.67      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.50/0.67      inference('demod', [status(thm)], ['4', '5'])).
% 0.50/0.67  thf(t100_xboole_1, axiom,
% 0.50/0.67    (![A:$i,B:$i]:
% 0.50/0.67     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.50/0.67  thf('7', plain,
% 0.50/0.67      (![X8 : $i, X9 : $i]:
% 0.50/0.67         ((k4_xboole_0 @ X8 @ X9)
% 0.50/0.67           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.50/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.67  thf('8', plain,
% 0.50/0.67      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.50/0.67         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.50/0.67      inference('sup+', [status(thm)], ['6', '7'])).
% 0.50/0.67  thf(t39_xboole_1, axiom,
% 0.50/0.67    (![A:$i,B:$i]:
% 0.50/0.67     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.50/0.67  thf('9', plain,
% 0.50/0.67      (![X13 : $i, X14 : $i]:
% 0.50/0.67         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.50/0.67           = (k2_xboole_0 @ X13 @ X14))),
% 0.50/0.67      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.50/0.67  thf('10', plain,
% 0.50/0.67      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.50/0.67         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.50/0.67         = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.50/0.67      inference('sup+', [status(thm)], ['8', '9'])).
% 0.50/0.67  thf('11', plain,
% 0.50/0.67      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.50/0.67         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.50/0.67      inference('sup+', [status(thm)], ['6', '7'])).
% 0.50/0.67  thf('12', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.67  thf(t94_xboole_1, axiom,
% 0.50/0.67    (![A:$i,B:$i]:
% 0.50/0.67     ( ( k2_xboole_0 @ A @ B ) =
% 0.50/0.67       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.50/0.67  thf('13', plain,
% 0.50/0.67      (![X19 : $i, X20 : $i]:
% 0.50/0.67         ((k2_xboole_0 @ X19 @ X20)
% 0.50/0.67           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 0.50/0.67              (k3_xboole_0 @ X19 @ X20)))),
% 0.50/0.67      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.50/0.67  thf(t91_xboole_1, axiom,
% 0.50/0.67    (![A:$i,B:$i,C:$i]:
% 0.50/0.67     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.50/0.67       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.50/0.67  thf('14', plain,
% 0.50/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.50/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.50/0.67           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.50/0.67      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.67  thf('15', plain,
% 0.50/0.67      (![X19 : $i, X20 : $i]:
% 0.50/0.67         ((k2_xboole_0 @ X19 @ X20)
% 0.50/0.67           = (k5_xboole_0 @ X19 @ 
% 0.50/0.67              (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X19 @ X20))))),
% 0.50/0.67      inference('demod', [status(thm)], ['13', '14'])).
% 0.50/0.67  thf('16', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]:
% 0.50/0.67         ((k2_xboole_0 @ X0 @ X1)
% 0.50/0.67           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.50/0.67      inference('sup+', [status(thm)], ['12', '15'])).
% 0.50/0.67  thf('17', plain,
% 0.50/0.67      (![X8 : $i, X9 : $i]:
% 0.50/0.67         ((k4_xboole_0 @ X8 @ X9)
% 0.50/0.67           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.50/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.67  thf('18', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]:
% 0.50/0.67         ((k2_xboole_0 @ X0 @ X1)
% 0.50/0.67           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.50/0.67      inference('demod', [status(thm)], ['16', '17'])).
% 0.50/0.67  thf('19', plain,
% 0.50/0.67      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.50/0.67         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.50/0.67            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.50/0.67      inference('sup+', [status(thm)], ['11', '18'])).
% 0.50/0.67  thf(d10_xboole_0, axiom,
% 0.50/0.67    (![A:$i,B:$i]:
% 0.50/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.67  thf('20', plain,
% 0.50/0.67      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.50/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.67  thf('21', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.50/0.67      inference('simplify', [status(thm)], ['20'])).
% 0.50/0.67  thf('22', plain,
% 0.50/0.67      (![X10 : $i, X11 : $i]:
% 0.50/0.67         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.50/0.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.67  thf('23', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.50/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.50/0.67  thf('24', plain,
% 0.50/0.67      (![X8 : $i, X9 : $i]:
% 0.50/0.67         ((k4_xboole_0 @ X8 @ X9)
% 0.50/0.67           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.50/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.67  thf('25', plain,
% 0.50/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.67      inference('sup+', [status(thm)], ['23', '24'])).
% 0.50/0.67  thf('26', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.50/0.67      inference('simplify', [status(thm)], ['20'])).
% 0.50/0.67  thf(l32_xboole_1, axiom,
% 0.50/0.67    (![A:$i,B:$i]:
% 0.50/0.67     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.50/0.67  thf('27', plain,
% 0.50/0.67      (![X5 : $i, X7 : $i]:
% 0.50/0.67         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.50/0.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.50/0.67  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.67      inference('sup-', [status(thm)], ['26', '27'])).
% 0.50/0.67  thf('29', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.67      inference('sup+', [status(thm)], ['25', '28'])).
% 0.50/0.67  thf('30', plain,
% 0.50/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.50/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.50/0.67           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.50/0.67      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.67  thf('31', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]:
% 0.50/0.67         ((k1_xboole_0)
% 0.50/0.67           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.50/0.67      inference('sup+', [status(thm)], ['29', '30'])).
% 0.50/0.67  thf('32', plain,
% 0.50/0.67      (((k1_xboole_0)
% 0.50/0.67         = (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.50/0.67      inference('sup+', [status(thm)], ['19', '31'])).
% 0.50/0.67  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.67      inference('sup+', [status(thm)], ['25', '28'])).
% 0.50/0.67  thf('34', plain,
% 0.50/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.50/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.50/0.67           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.50/0.67      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.67  thf('35', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]:
% 0.50/0.67         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.50/0.67           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.67      inference('sup+', [status(thm)], ['33', '34'])).
% 0.50/0.67  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.50/0.67  thf('36', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.50/0.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.50/0.67  thf('37', plain,
% 0.50/0.67      (![X10 : $i, X11 : $i]:
% 0.50/0.67         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.50/0.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.67  thf('38', plain,
% 0.50/0.67      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.50/0.67      inference('sup-', [status(thm)], ['36', '37'])).
% 0.50/0.67  thf('39', plain,
% 0.50/0.67      (![X19 : $i, X20 : $i]:
% 0.50/0.67         ((k2_xboole_0 @ X19 @ X20)
% 0.50/0.67           = (k5_xboole_0 @ X19 @ 
% 0.50/0.67              (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X19 @ X20))))),
% 0.50/0.67      inference('demod', [status(thm)], ['13', '14'])).
% 0.50/0.67  thf('40', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.50/0.67           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.50/0.67      inference('sup+', [status(thm)], ['38', '39'])).
% 0.50/0.67  thf(t5_boole, axiom,
% 0.50/0.67    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.50/0.67  thf('41', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.50/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.50/0.67  thf('42', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.67      inference('demod', [status(thm)], ['40', '41'])).
% 0.50/0.67  thf('43', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]:
% 0.50/0.67         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.50/0.67           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.67      inference('demod', [status(thm)], ['35', '42'])).
% 0.50/0.67  thf('44', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.67      inference('sup+', [status(thm)], ['25', '28'])).
% 0.50/0.67  thf('45', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]:
% 0.50/0.67         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.50/0.67           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.67      inference('demod', [status(thm)], ['35', '42'])).
% 0.50/0.67  thf('46', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.50/0.67      inference('sup+', [status(thm)], ['44', '45'])).
% 0.50/0.67  thf('47', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.50/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.50/0.67  thf('48', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.67      inference('sup+', [status(thm)], ['46', '47'])).
% 0.50/0.67  thf('49', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]:
% 0.50/0.67         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.67      inference('demod', [status(thm)], ['43', '48'])).
% 0.50/0.67  thf('50', plain,
% 0.50/0.67      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.50/0.67         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.50/0.67      inference('sup+', [status(thm)], ['32', '49'])).
% 0.50/0.67  thf('51', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.50/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.50/0.67  thf('52', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.50/0.67      inference('demod', [status(thm)], ['50', '51'])).
% 0.50/0.67  thf('53', plain,
% 0.50/0.67      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.50/0.67         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (sk_B))),
% 0.50/0.67      inference('demod', [status(thm)], ['10', '52'])).
% 0.50/0.67  thf('54', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]:
% 0.50/0.67         ((k1_xboole_0)
% 0.50/0.67           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.50/0.67      inference('sup+', [status(thm)], ['29', '30'])).
% 0.50/0.67  thf('55', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]:
% 0.50/0.67         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.67      inference('demod', [status(thm)], ['43', '48'])).
% 0.50/0.67  thf('56', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]:
% 0.50/0.67         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.50/0.67           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.50/0.67      inference('sup+', [status(thm)], ['54', '55'])).
% 0.50/0.67  thf('57', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.50/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.50/0.67  thf('58', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]:
% 0.50/0.67         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.50/0.67      inference('demod', [status(thm)], ['56', '57'])).
% 0.50/0.67  thf('59', plain,
% 0.50/0.67      (![X19 : $i, X20 : $i]:
% 0.50/0.67         ((k2_xboole_0 @ X19 @ X20)
% 0.50/0.67           = (k5_xboole_0 @ X19 @ 
% 0.50/0.67              (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X19 @ X20))))),
% 0.50/0.67      inference('demod', [status(thm)], ['13', '14'])).
% 0.50/0.67  thf('60', plain,
% 0.50/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.50/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.50/0.67           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.50/0.67      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.67  thf('61', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.67         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.50/0.67           = (k5_xboole_0 @ X1 @ 
% 0.50/0.67              (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X2)))),
% 0.50/0.67      inference('sup+', [status(thm)], ['59', '60'])).
% 0.50/0.67  thf('62', plain,
% 0.50/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.50/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.50/0.67           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.50/0.67      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.67  thf('63', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.67         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.50/0.67           = (k5_xboole_0 @ X1 @ 
% 0.50/0.67              (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))))),
% 0.50/0.67      inference('demod', [status(thm)], ['61', '62'])).
% 0.50/0.67  thf('64', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]:
% 0.50/0.67         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.50/0.67           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.50/0.67      inference('sup+', [status(thm)], ['58', '63'])).
% 0.50/0.67  thf('65', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]:
% 0.50/0.67         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.50/0.67      inference('demod', [status(thm)], ['56', '57'])).
% 0.50/0.67  thf('66', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]:
% 0.50/0.67         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.67      inference('demod', [status(thm)], ['43', '48'])).
% 0.50/0.67  thf('67', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.50/0.67      inference('sup+', [status(thm)], ['65', '66'])).
% 0.50/0.67  thf('68', plain,
% 0.50/0.67      (![X8 : $i, X9 : $i]:
% 0.50/0.67         ((k4_xboole_0 @ X8 @ X9)
% 0.50/0.67           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.50/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.67  thf('69', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]:
% 0.50/0.67         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.50/0.67           = (k4_xboole_0 @ X1 @ X0))),
% 0.50/0.67      inference('demod', [status(thm)], ['64', '67', '68'])).
% 0.50/0.67  thf('70', plain,
% 0.50/0.67      (((k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 0.50/0.67         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.50/0.67            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.50/0.67      inference('sup+', [status(thm)], ['53', '69'])).
% 0.50/0.67  thf('71', plain,
% 0.50/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.50/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.50/0.67           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.50/0.67      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.67  thf('72', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.50/0.67      inference('sup+', [status(thm)], ['65', '66'])).
% 0.50/0.67  thf('73', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]:
% 0.50/0.67         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.67      inference('demod', [status(thm)], ['43', '48'])).
% 0.50/0.67  thf('74', plain,
% 0.50/0.67      (((k1_tarski @ sk_A)
% 0.50/0.67         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.50/0.67            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.50/0.67      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.50/0.67  thf('75', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]:
% 0.50/0.67         ((k2_xboole_0 @ X0 @ X1)
% 0.50/0.67           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.50/0.67      inference('demod', [status(thm)], ['16', '17'])).
% 0.50/0.67  thf('76', plain,
% 0.50/0.67      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.50/0.67         (k1_tarski @ sk_A))
% 0.50/0.67         = (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.50/0.67            (k1_tarski @ sk_A)))),
% 0.50/0.67      inference('sup+', [status(thm)], ['74', '75'])).
% 0.50/0.67  thf('77', plain,
% 0.50/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.50/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.50/0.67           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.50/0.67      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.67  thf('78', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.67      inference('sup+', [status(thm)], ['25', '28'])).
% 0.50/0.67  thf('79', plain,
% 0.50/0.67      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.50/0.67      inference('sup+', [status(thm)], ['65', '66'])).
% 0.50/0.67  thf('80', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.67      inference('demod', [status(thm)], ['40', '41'])).
% 0.50/0.67  thf('81', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.67      inference('sup+', [status(thm)], ['46', '47'])).
% 0.50/0.67  thf('82', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.67      inference('demod', [status(thm)], ['80', '81'])).
% 0.50/0.67  thf('83', plain,
% 0.50/0.67      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.50/0.67         (k1_tarski @ sk_A)) = (sk_B))),
% 0.50/0.67      inference('demod', [status(thm)], ['76', '77', '78', '79', '82'])).
% 0.50/0.67  thf('84', plain,
% 0.50/0.67      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.50/0.67         (k1_tarski @ sk_A)) != (sk_B))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('85', plain,
% 0.50/0.67      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.50/0.67         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.50/0.67      inference('sup+', [status(thm)], ['6', '7'])).
% 0.50/0.67  thf('86', plain,
% 0.50/0.67      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.50/0.67         (k1_tarski @ sk_A)) != (sk_B))),
% 0.50/0.67      inference('demod', [status(thm)], ['84', '85'])).
% 0.50/0.67  thf('87', plain, ($false),
% 0.50/0.67      inference('simplify_reflect-', [status(thm)], ['83', '86'])).
% 0.50/0.67  
% 0.50/0.67  % SZS output end Refutation
% 0.50/0.67  
% 0.50/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
