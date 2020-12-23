%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1q5D9ZvJv7

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:55 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 161 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  580 (1119 expanded)
%              Number of equality atoms :   64 ( 125 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ X36 ) ) ),
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

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['9','26'])).

thf('28',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('37',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['8','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('44',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('50',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('58',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['48','49','56','57'])).

thf('59',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('61',plain,(
    ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1q5D9ZvJv7
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:05:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.44/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.65  % Solved by: fo/fo7.sh
% 0.44/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.65  % done 352 iterations in 0.196s
% 0.44/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.65  % SZS output start Refutation
% 0.44/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.65  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.44/0.65  thf(t140_zfmisc_1, conjecture,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( r2_hidden @ A @ B ) =>
% 0.44/0.65       ( ( k2_xboole_0 @
% 0.44/0.65           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.44/0.65         ( B ) ) ))).
% 0.44/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.65    (~( ![A:$i,B:$i]:
% 0.44/0.65        ( ( r2_hidden @ A @ B ) =>
% 0.44/0.65          ( ( k2_xboole_0 @
% 0.44/0.65              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.44/0.65            ( B ) ) ) )),
% 0.44/0.65    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.44/0.65  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(l1_zfmisc_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.44/0.65  thf('1', plain,
% 0.44/0.65      (![X34 : $i, X36 : $i]:
% 0.44/0.65         ((r1_tarski @ (k1_tarski @ X34) @ X36) | ~ (r2_hidden @ X34 @ X36))),
% 0.44/0.65      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.44/0.65  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.44/0.65      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.65  thf(t28_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.44/0.65  thf('3', plain,
% 0.44/0.65      (![X10 : $i, X11 : $i]:
% 0.44/0.65         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.44/0.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.65  thf('4', plain,
% 0.44/0.65      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.44/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.44/0.65  thf(commutativity_k3_xboole_0, axiom,
% 0.44/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.44/0.65  thf('5', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.65  thf('6', plain,
% 0.44/0.65      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.44/0.65      inference('demod', [status(thm)], ['4', '5'])).
% 0.44/0.65  thf(t100_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.44/0.65  thf('7', plain,
% 0.44/0.65      (![X8 : $i, X9 : $i]:
% 0.44/0.65         ((k4_xboole_0 @ X8 @ X9)
% 0.44/0.65           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.65  thf('8', plain,
% 0.44/0.65      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.44/0.65         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('sup+', [status(thm)], ['6', '7'])).
% 0.44/0.65  thf('9', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.65  thf(d10_xboole_0, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.65  thf('10', plain,
% 0.44/0.65      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.44/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.65  thf('11', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.44/0.65      inference('simplify', [status(thm)], ['10'])).
% 0.44/0.65  thf(l32_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.65  thf('12', plain,
% 0.44/0.65      (![X5 : $i, X7 : $i]:
% 0.44/0.65         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.44/0.65      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.44/0.65  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.65  thf(t49_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.44/0.65       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.44/0.65  thf('14', plain,
% 0.44/0.65      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.65         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 0.44/0.65           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 0.44/0.65      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.44/0.65  thf('15', plain,
% 0.44/0.65      (![X5 : $i, X6 : $i]:
% 0.44/0.65         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.44/0.65      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.44/0.65  thf('16', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.44/0.65          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.65  thf('17', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (((k3_xboole_0 @ X1 @ k1_xboole_0) != (k1_xboole_0))
% 0.44/0.65          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['13', '16'])).
% 0.44/0.65  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.65  thf(t36_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.44/0.65  thf('19', plain,
% 0.44/0.65      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.44/0.65      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.44/0.65  thf('20', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.44/0.65      inference('sup+', [status(thm)], ['18', '19'])).
% 0.44/0.65  thf('21', plain,
% 0.44/0.65      (![X10 : $i, X11 : $i]:
% 0.44/0.65         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.44/0.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.65  thf('22', plain,
% 0.44/0.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['20', '21'])).
% 0.44/0.65  thf('23', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.65  thf('24', plain,
% 0.44/0.65      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['22', '23'])).
% 0.44/0.65  thf('25', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.65          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['17', '24'])).
% 0.44/0.65  thf('26', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.44/0.65      inference('simplify', [status(thm)], ['25'])).
% 0.44/0.65  thf('27', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.44/0.65      inference('sup+', [status(thm)], ['9', '26'])).
% 0.44/0.65  thf('28', plain,
% 0.44/0.65      (![X5 : $i, X7 : $i]:
% 0.44/0.65         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.44/0.65      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.44/0.65  thf('29', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.44/0.65  thf('30', plain,
% 0.44/0.65      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.65         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 0.44/0.65           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 0.44/0.65      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.44/0.65  thf('31', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.44/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.44/0.65  thf('32', plain,
% 0.44/0.65      (![X8 : $i, X9 : $i]:
% 0.44/0.65         ((k4_xboole_0 @ X8 @ X9)
% 0.44/0.65           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.65  thf('33', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.44/0.65           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['31', '32'])).
% 0.44/0.65  thf('34', plain,
% 0.44/0.65      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['22', '23'])).
% 0.44/0.65  thf('35', plain,
% 0.44/0.65      (![X8 : $i, X9 : $i]:
% 0.44/0.65         ((k4_xboole_0 @ X8 @ X9)
% 0.44/0.65           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.65  thf('36', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['34', '35'])).
% 0.44/0.65  thf(t3_boole, axiom,
% 0.44/0.65    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.44/0.65  thf('37', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.44/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.65  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['36', '37'])).
% 0.44/0.65  thf('39', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['33', '38'])).
% 0.44/0.65  thf('40', plain,
% 0.44/0.65      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.44/0.65         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (k1_tarski @ sk_A))),
% 0.44/0.65      inference('sup+', [status(thm)], ['8', '39'])).
% 0.44/0.65  thf('41', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.65  thf(t94_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( k2_xboole_0 @ A @ B ) =
% 0.44/0.65       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.44/0.65  thf('42', plain,
% 0.44/0.65      (![X22 : $i, X23 : $i]:
% 0.44/0.65         ((k2_xboole_0 @ X22 @ X23)
% 0.44/0.65           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 0.44/0.65              (k3_xboole_0 @ X22 @ X23)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.44/0.65  thf(t91_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.44/0.65       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.44/0.65  thf('43', plain,
% 0.44/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.44/0.65         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.44/0.65           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.44/0.65  thf('44', plain,
% 0.44/0.65      (![X22 : $i, X23 : $i]:
% 0.44/0.65         ((k2_xboole_0 @ X22 @ X23)
% 0.44/0.65           = (k5_xboole_0 @ X22 @ 
% 0.44/0.65              (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X22 @ X23))))),
% 0.44/0.65      inference('demod', [status(thm)], ['42', '43'])).
% 0.44/0.65  thf('45', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((k2_xboole_0 @ X0 @ X1)
% 0.44/0.65           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.44/0.65      inference('sup+', [status(thm)], ['41', '44'])).
% 0.44/0.65  thf('46', plain,
% 0.44/0.65      (![X8 : $i, X9 : $i]:
% 0.44/0.65         ((k4_xboole_0 @ X8 @ X9)
% 0.44/0.65           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.65  thf('47', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((k2_xboole_0 @ X0 @ X1)
% 0.44/0.65           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.44/0.65      inference('demod', [status(thm)], ['45', '46'])).
% 0.44/0.65  thf('48', plain,
% 0.44/0.65      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.44/0.65         (k1_tarski @ sk_A))
% 0.44/0.65         = (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.44/0.65            (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('sup+', [status(thm)], ['40', '47'])).
% 0.44/0.65  thf('49', plain,
% 0.44/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.44/0.65         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.44/0.65           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.44/0.65  thf('50', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.44/0.65      inference('simplify', [status(thm)], ['10'])).
% 0.44/0.65  thf('51', plain,
% 0.44/0.65      (![X10 : $i, X11 : $i]:
% 0.44/0.65         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.44/0.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.65  thf('52', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['50', '51'])).
% 0.44/0.65  thf('53', plain,
% 0.44/0.65      (![X8 : $i, X9 : $i]:
% 0.44/0.65         ((k4_xboole_0 @ X8 @ X9)
% 0.44/0.65           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.65  thf('54', plain,
% 0.44/0.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['52', '53'])).
% 0.44/0.65  thf('55', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.65  thf('56', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['54', '55'])).
% 0.44/0.65  thf('57', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['36', '37'])).
% 0.44/0.65  thf('58', plain,
% 0.44/0.65      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.44/0.65         (k1_tarski @ sk_A)) = (sk_B))),
% 0.44/0.65      inference('demod', [status(thm)], ['48', '49', '56', '57'])).
% 0.44/0.65  thf('59', plain,
% 0.44/0.65      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.44/0.65         (k1_tarski @ sk_A)) != (sk_B))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('60', plain,
% 0.44/0.65      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.44/0.65         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('sup+', [status(thm)], ['6', '7'])).
% 0.44/0.65  thf('61', plain,
% 0.44/0.65      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.44/0.65         (k1_tarski @ sk_A)) != (sk_B))),
% 0.44/0.65      inference('demod', [status(thm)], ['59', '60'])).
% 0.44/0.65  thf('62', plain, ($false),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['58', '61'])).
% 0.44/0.65  
% 0.44/0.65  % SZS output end Refutation
% 0.44/0.65  
% 0.44/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
