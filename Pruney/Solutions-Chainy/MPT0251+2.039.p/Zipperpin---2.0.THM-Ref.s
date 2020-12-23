%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Edt6eX9Cvp

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:06 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 118 expanded)
%              Number of leaves         :   26 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  478 ( 762 expanded)
%              Number of equality atoms :   43 (  75 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('6',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('11',plain,(
    ! [X36: $i,X38: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X36 ) @ X38 )
      | ~ ( r2_hidden @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('26',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','19','42'])).

thf('44',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','43'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('46',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('48',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('51',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Edt6eX9Cvp
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 597 iterations in 0.182s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.63  thf(d10_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.63  thf('0', plain,
% 0.46/0.63      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.63  thf('1', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.46/0.63      inference('simplify', [status(thm)], ['0'])).
% 0.46/0.63  thf(t28_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (![X16 : $i, X17 : $i]:
% 0.46/0.63         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.46/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.63  thf('3', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.63  thf(t22_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      (![X14 : $i, X15 : $i]:
% 0.46/0.63         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 0.46/0.63      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.46/0.63  thf('5', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['3', '4'])).
% 0.46/0.63  thf(t46_zfmisc_1, conjecture,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( r2_hidden @ A @ B ) =>
% 0.46/0.63       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i,B:$i]:
% 0.46/0.63        ( ( r2_hidden @ A @ B ) =>
% 0.46/0.63          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.46/0.63  thf('6', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t7_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.63  thf('7', plain,
% 0.46/0.63      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.46/0.63      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.63  thf(d3_tarski, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.63          | (r2_hidden @ X0 @ X2)
% 0.46/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      (![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['6', '9'])).
% 0.46/0.63  thf(l1_zfmisc_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      (![X36 : $i, X38 : $i]:
% 0.46/0.63         ((r1_tarski @ (k1_tarski @ X36) @ X38) | ~ (r2_hidden @ X36 @ X38))),
% 0.46/0.63      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      (![X0 : $i]: (r1_tarski @ (k1_tarski @ sk_A) @ (k2_xboole_0 @ sk_B @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.63  thf('13', plain,
% 0.46/0.63      (![X16 : $i, X17 : $i]:
% 0.46/0.63         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.46/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.63  thf('14', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_xboole_0 @ sk_B @ X0))
% 0.46/0.64           = (k1_tarski @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.64  thf(t100_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X11 : $i, X12 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X11 @ X12)
% 0.46/0.64           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_xboole_0 @ sk_B @ X0))
% 0.46/0.64           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['14', '15'])).
% 0.46/0.64  thf('17', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X11 : $i, X12 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X11 @ X12)
% 0.46/0.64           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X1 : $i, X3 : $i]:
% 0.46/0.64         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.64  thf(t1_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.46/0.64       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.64         ((r2_hidden @ X4 @ X5)
% 0.46/0.64          | (r2_hidden @ X4 @ X6)
% 0.46/0.64          | ~ (r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.46/0.64          | (r2_hidden @ X1 @ X0)
% 0.46/0.64          | (r2_hidden @ X1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X4 @ X5)
% 0.46/0.64          | ~ (r2_hidden @ X4 @ X6)
% 0.46/0.64          | ~ (r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.46/0.64          | ~ (r2_hidden @ X1 @ X0)
% 0.46/0.64          | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X1 @ X0)
% 0.46/0.64          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['27'])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('clc', [status(thm)], ['24', '28'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.46/0.64      inference('sup-', [status(thm)], ['20', '29'])).
% 0.46/0.64  thf(commutativity_k2_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i]:
% 0.46/0.64         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.64  thf(l51_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X39 : $i, X40 : $i]:
% 0.46/0.64         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.46/0.64      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['31', '32'])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X39 : $i, X40 : $i]:
% 0.46/0.64         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.46/0.64      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.64  thf(t1_boole, axiom,
% 0.46/0.64    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.64  thf('36', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.64  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['35', '36'])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.64  thf('39', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.46/0.64      inference('sup+', [status(thm)], ['37', '38'])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X8 : $i, X10 : $i]:
% 0.46/0.64         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.64  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['30', '41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_xboole_0 @ sk_B @ X0))
% 0.46/0.64           = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['16', '19', '42'])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['5', '43'])).
% 0.46/0.64  thf(t39_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 0.46/0.64           = (k2_xboole_0 @ X18 @ X19))),
% 0.46/0.64      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.46/0.64         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['44', '45'])).
% 0.46/0.64  thf('47', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.64  thf('48', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.64  thf('49', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.64  thf('51', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.64  thf('52', plain, ($false),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['48', '51'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
