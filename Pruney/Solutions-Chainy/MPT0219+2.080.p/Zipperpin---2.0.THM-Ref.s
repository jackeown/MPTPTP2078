%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WIZ3dYyscP

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:14 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 431 expanded)
%              Number of leaves         :   27 ( 152 expanded)
%              Depth                    :   23
%              Number of atoms          :  552 (3215 expanded)
%              Number of equality atoms :   62 ( 270 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('18',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','21'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','21'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','37'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','21'])).

thf('48',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('54',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('59',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53 = X52 )
      | ~ ( r1_tarski @ ( k1_tarski @ X53 ) @ ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('60',plain,(
    sk_B_1 = sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WIZ3dYyscP
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:11:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 658 iterations in 0.195s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(t13_zfmisc_1, conjecture,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.47/0.65         ( k1_tarski @ A ) ) =>
% 0.47/0.65       ( ( A ) = ( B ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i,B:$i]:
% 0.47/0.65        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.47/0.65            ( k1_tarski @ A ) ) =>
% 0.47/0.65          ( ( A ) = ( B ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.47/0.65  thf('0', plain,
% 0.47/0.65      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.47/0.65         = (k1_tarski @ sk_A))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(t98_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.47/0.65  thf('1', plain,
% 0.47/0.65      (![X22 : $i, X23 : $i]:
% 0.47/0.65         ((k2_xboole_0 @ X22 @ X23)
% 0.47/0.65           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.47/0.65  thf(idempotence_k3_xboole_0, axiom,
% 0.47/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.47/0.65  thf('2', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.47/0.65      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.47/0.65  thf(t100_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.47/0.65  thf('3', plain,
% 0.47/0.65      (![X8 : $i, X9 : $i]:
% 0.47/0.65         ((k4_xboole_0 @ X8 @ X9)
% 0.47/0.65           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.65  thf('4', plain,
% 0.47/0.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['2', '3'])).
% 0.47/0.65  thf(t36_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.47/0.65  thf('5', plain,
% 0.47/0.65      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.47/0.65      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.47/0.65  thf(t28_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.47/0.65  thf('6', plain,
% 0.47/0.65      (![X12 : $i, X13 : $i]:
% 0.47/0.65         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.47/0.65  thf('7', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.47/0.65           = (k4_xboole_0 @ X0 @ X1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.65  thf(commutativity_k3_xboole_0, axiom,
% 0.47/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.47/0.65  thf('8', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.65  thf('9', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.47/0.65           = (k4_xboole_0 @ X0 @ X1))),
% 0.47/0.65      inference('demod', [status(thm)], ['7', '8'])).
% 0.47/0.65  thf(t79_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.47/0.65  thf('10', plain,
% 0.47/0.65      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 0.47/0.65      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.47/0.65  thf(t4_xboole_0, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.47/0.65            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.47/0.65  thf('11', plain,
% 0.47/0.65      (![X3 : $i, X4 : $i]:
% 0.47/0.65         ((r1_xboole_0 @ X3 @ X4)
% 0.47/0.65          | (r2_hidden @ (sk_C @ X4 @ X3) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.47/0.65  thf('12', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.65  thf('13', plain,
% 0.47/0.65      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.47/0.65         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.47/0.65          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.47/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.47/0.65  thf('14', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.47/0.65          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.65  thf('15', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['11', '14'])).
% 0.47/0.65  thf('16', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['10', '15'])).
% 0.47/0.65  thf(t7_xboole_0, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.65          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.47/0.65  thf('17', plain,
% 0.47/0.65      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.65  thf('18', plain,
% 0.47/0.65      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.47/0.65         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.47/0.65          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.47/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.47/0.65  thf('19', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.65  thf('20', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['16', '19'])).
% 0.47/0.65  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['9', '20'])).
% 0.47/0.65  thf('22', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['4', '21'])).
% 0.47/0.65  thf(t91_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.47/0.65       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.47/0.65  thf('23', plain,
% 0.47/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.65         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.47/0.65           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.47/0.65  thf('24', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.47/0.65           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['22', '23'])).
% 0.47/0.65  thf('25', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['16', '19'])).
% 0.47/0.65  thf(t17_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.47/0.65  thf('26', plain,
% 0.47/0.65      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.47/0.65      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.47/0.65  thf('27', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.47/0.65      inference('sup+', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('28', plain,
% 0.47/0.65      (![X12 : $i, X13 : $i]:
% 0.47/0.65         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.47/0.65  thf('29', plain,
% 0.47/0.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.65  thf('30', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.65  thf('31', plain,
% 0.47/0.65      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['29', '30'])).
% 0.47/0.65  thf('32', plain,
% 0.47/0.65      (![X8 : $i, X9 : $i]:
% 0.47/0.65         ((k4_xboole_0 @ X8 @ X9)
% 0.47/0.65           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.65  thf('33', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['31', '32'])).
% 0.47/0.65  thf(t5_boole, axiom,
% 0.47/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.65  thf('34', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.47/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.47/0.65  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['33', '34'])).
% 0.47/0.65  thf('36', plain,
% 0.47/0.65      (![X22 : $i, X23 : $i]:
% 0.47/0.65         ((k2_xboole_0 @ X22 @ X23)
% 0.47/0.65           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.47/0.65  thf('37', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['35', '36'])).
% 0.47/0.65  thf('38', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.47/0.65           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.47/0.65      inference('demod', [status(thm)], ['24', '37'])).
% 0.47/0.65  thf('39', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['4', '21'])).
% 0.47/0.65  thf('40', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.47/0.65           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.47/0.65      inference('demod', [status(thm)], ['24', '37'])).
% 0.47/0.65  thf('41', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['39', '40'])).
% 0.47/0.65  thf('42', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.47/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.47/0.65  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['41', '42'])).
% 0.47/0.65  thf('44', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.47/0.65      inference('demod', [status(thm)], ['38', '43'])).
% 0.47/0.65  thf('45', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((k4_xboole_0 @ X0 @ X1)
% 0.47/0.65           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['1', '44'])).
% 0.47/0.65  thf('46', plain,
% 0.47/0.65      (((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.47/0.65         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['0', '45'])).
% 0.47/0.65  thf('47', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['4', '21'])).
% 0.47/0.65  thf('48', plain,
% 0.47/0.65      (((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.47/0.65         = (k1_xboole_0))),
% 0.47/0.65      inference('demod', [status(thm)], ['46', '47'])).
% 0.47/0.65  thf('49', plain,
% 0.47/0.65      (![X8 : $i, X9 : $i]:
% 0.47/0.65         ((k4_xboole_0 @ X8 @ X9)
% 0.47/0.65           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.65  thf('50', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.47/0.65      inference('demod', [status(thm)], ['38', '43'])).
% 0.47/0.65  thf('51', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((k3_xboole_0 @ X1 @ X0)
% 0.47/0.65           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['49', '50'])).
% 0.47/0.65  thf('52', plain,
% 0.47/0.65      (((k3_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.47/0.65         = (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ k1_xboole_0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['48', '51'])).
% 0.47/0.65  thf('53', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.47/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.47/0.65  thf('54', plain,
% 0.47/0.65      (((k3_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.47/0.65         = (k1_tarski @ sk_B_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['52', '53'])).
% 0.47/0.65  thf('55', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.65  thf('56', plain,
% 0.47/0.65      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.47/0.65      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.47/0.65  thf('57', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.47/0.65      inference('sup+', [status(thm)], ['55', '56'])).
% 0.47/0.65  thf('58', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))),
% 0.47/0.65      inference('sup+', [status(thm)], ['54', '57'])).
% 0.47/0.65  thf(t6_zfmisc_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.47/0.65       ( ( A ) = ( B ) ) ))).
% 0.47/0.65  thf('59', plain,
% 0.47/0.65      (![X52 : $i, X53 : $i]:
% 0.47/0.65         (((X53) = (X52))
% 0.47/0.65          | ~ (r1_tarski @ (k1_tarski @ X53) @ (k1_tarski @ X52)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.47/0.65  thf('60', plain, (((sk_B_1) = (sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['58', '59'])).
% 0.47/0.65  thf('61', plain, (((sk_A) != (sk_B_1))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('62', plain, ($false),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 0.47/0.65  
% 0.47/0.65  % SZS output end Refutation
% 0.47/0.65  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
