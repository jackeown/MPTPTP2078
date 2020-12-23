%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DgBGZ0NmgH

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:49 EST 2020

% Result     : Theorem 2.55s
% Output     : Refutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 172 expanded)
%              Number of leaves         :   19 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  571 (1298 expanded)
%              Number of equality atoms :   60 ( 129 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t87_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
          = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_B )
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) )
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_A )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['8','19'])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup+',[status(thm)],['40','48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['49','52'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('54',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) )
 != ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','55'])).

thf('57',plain,(
    $false ),
    inference(simplify,[status(thm)],['56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DgBGZ0NmgH
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:10:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.55/2.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.55/2.72  % Solved by: fo/fo7.sh
% 2.55/2.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.55/2.72  % done 4077 iterations in 2.235s
% 2.55/2.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.55/2.72  % SZS output start Refutation
% 2.55/2.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.55/2.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.55/2.72  thf(sk_A_type, type, sk_A: $i).
% 2.55/2.72  thf(sk_C_type, type, sk_C: $i).
% 2.55/2.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.55/2.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.55/2.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.55/2.72  thf(sk_B_type, type, sk_B: $i).
% 2.55/2.72  thf(t87_xboole_1, conjecture,
% 2.55/2.72    (![A:$i,B:$i,C:$i]:
% 2.55/2.72     ( ( r1_xboole_0 @ A @ B ) =>
% 2.55/2.72       ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 2.55/2.72         ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ))).
% 2.55/2.72  thf(zf_stmt_0, negated_conjecture,
% 2.55/2.72    (~( ![A:$i,B:$i,C:$i]:
% 2.55/2.72        ( ( r1_xboole_0 @ A @ B ) =>
% 2.55/2.72          ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 2.55/2.72            ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )),
% 2.55/2.72    inference('cnf.neg', [status(esa)], [t87_xboole_1])).
% 2.55/2.72  thf('0', plain,
% 2.55/2.72      (((k2_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_B)
% 2.55/2.72         != (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf(commutativity_k2_xboole_0, axiom,
% 2.55/2.72    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.55/2.72  thf('1', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.55/2.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.55/2.72  thf('2', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.55/2.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.55/2.72  thf('3', plain,
% 2.55/2.72      (((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A))
% 2.55/2.72         != (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 2.55/2.72      inference('demod', [status(thm)], ['0', '1', '2'])).
% 2.55/2.72  thf('4', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf(t83_xboole_1, axiom,
% 2.55/2.72    (![A:$i,B:$i]:
% 2.55/2.72     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.55/2.72  thf('5', plain,
% 2.55/2.72      (![X21 : $i, X22 : $i]:
% 2.55/2.72         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 2.55/2.72      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.55/2.72  thf('6', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 2.55/2.72      inference('sup-', [status(thm)], ['4', '5'])).
% 2.55/2.72  thf(t49_xboole_1, axiom,
% 2.55/2.72    (![A:$i,B:$i,C:$i]:
% 2.55/2.72     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 2.55/2.72       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 2.55/2.72  thf('7', plain,
% 2.55/2.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.55/2.72         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 2.55/2.72           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 2.55/2.72      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.55/2.72  thf('8', plain,
% 2.55/2.72      (![X0 : $i]:
% 2.55/2.72         ((k3_xboole_0 @ X0 @ sk_A)
% 2.55/2.72           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B))),
% 2.55/2.72      inference('sup+', [status(thm)], ['6', '7'])).
% 2.55/2.72  thf(t48_xboole_1, axiom,
% 2.55/2.72    (![A:$i,B:$i]:
% 2.55/2.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.55/2.72  thf('9', plain,
% 2.55/2.72      (![X16 : $i, X17 : $i]:
% 2.55/2.72         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.55/2.72           = (k3_xboole_0 @ X16 @ X17))),
% 2.55/2.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.55/2.72  thf(t36_xboole_1, axiom,
% 2.55/2.72    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.55/2.72  thf('10', plain,
% 2.55/2.72      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 2.55/2.72      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.55/2.72  thf(t12_xboole_1, axiom,
% 2.55/2.72    (![A:$i,B:$i]:
% 2.55/2.72     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.55/2.72  thf('11', plain,
% 2.55/2.72      (![X2 : $i, X3 : $i]:
% 2.55/2.72         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 2.55/2.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.55/2.72  thf('12', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 2.55/2.72      inference('sup-', [status(thm)], ['10', '11'])).
% 2.55/2.72  thf('13', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.55/2.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.55/2.72  thf('14', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 2.55/2.72      inference('demod', [status(thm)], ['12', '13'])).
% 2.55/2.72  thf('15', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 2.55/2.72      inference('sup+', [status(thm)], ['9', '14'])).
% 2.55/2.72  thf('16', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.55/2.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.55/2.72  thf(t40_xboole_1, axiom,
% 2.55/2.72    (![A:$i,B:$i]:
% 2.55/2.72     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.55/2.72  thf('17', plain,
% 2.55/2.72      (![X8 : $i, X9 : $i]:
% 2.55/2.72         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 2.55/2.72           = (k4_xboole_0 @ X8 @ X9))),
% 2.55/2.72      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.55/2.72  thf('18', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 2.55/2.72           = (k4_xboole_0 @ X0 @ X1))),
% 2.55/2.72      inference('sup+', [status(thm)], ['16', '17'])).
% 2.55/2.72  thf('19', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         ((k4_xboole_0 @ X0 @ X0)
% 2.55/2.72           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 2.55/2.72      inference('sup+', [status(thm)], ['15', '18'])).
% 2.55/2.72  thf('20', plain,
% 2.55/2.72      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.55/2.72      inference('sup+', [status(thm)], ['8', '19'])).
% 2.55/2.72  thf('21', plain,
% 2.55/2.72      (![X8 : $i, X9 : $i]:
% 2.55/2.72         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 2.55/2.72           = (k4_xboole_0 @ X8 @ X9))),
% 2.55/2.72      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.55/2.72  thf('22', plain,
% 2.55/2.72      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 2.55/2.72      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.55/2.72  thf('23', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))),
% 2.55/2.72      inference('sup+', [status(thm)], ['21', '22'])).
% 2.55/2.72  thf(t43_xboole_1, axiom,
% 2.55/2.72    (![A:$i,B:$i,C:$i]:
% 2.55/2.72     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 2.55/2.72       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 2.55/2.72  thf('24', plain,
% 2.55/2.72      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.55/2.72         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 2.55/2.72          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 2.55/2.72      inference('cnf', [status(esa)], [t43_xboole_1])).
% 2.55/2.72  thf('25', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 2.55/2.72      inference('sup-', [status(thm)], ['23', '24'])).
% 2.55/2.72  thf('26', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 2.55/2.72      inference('demod', [status(thm)], ['12', '13'])).
% 2.55/2.72  thf('27', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 2.55/2.72           = (k4_xboole_0 @ X0 @ X1))),
% 2.55/2.72      inference('sup+', [status(thm)], ['16', '17'])).
% 2.55/2.72  thf('28', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         ((k4_xboole_0 @ X0 @ X0)
% 2.55/2.72           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 2.55/2.72      inference('sup+', [status(thm)], ['26', '27'])).
% 2.55/2.72  thf('29', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 2.55/2.72      inference('demod', [status(thm)], ['25', '28'])).
% 2.55/2.72  thf('30', plain,
% 2.55/2.72      (![X2 : $i, X3 : $i]:
% 2.55/2.72         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 2.55/2.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.55/2.72  thf('31', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 2.55/2.72      inference('sup-', [status(thm)], ['29', '30'])).
% 2.55/2.72  thf('32', plain,
% 2.55/2.72      (![X0 : $i]: ((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0) = (X0))),
% 2.55/2.72      inference('sup+', [status(thm)], ['20', '31'])).
% 2.55/2.72  thf('33', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 2.55/2.72      inference('sup-', [status(thm)], ['4', '5'])).
% 2.55/2.72  thf('34', plain,
% 2.55/2.72      (![X16 : $i, X17 : $i]:
% 2.55/2.72         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.55/2.72           = (k3_xboole_0 @ X16 @ X17))),
% 2.55/2.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.55/2.72  thf('35', plain,
% 2.55/2.72      (((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 2.55/2.72      inference('sup+', [status(thm)], ['33', '34'])).
% 2.55/2.72  thf('36', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 2.55/2.72      inference('sup-', [status(thm)], ['29', '30'])).
% 2.55/2.72  thf('37', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.55/2.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.55/2.72  thf('38', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1)) = (X0))),
% 2.55/2.72      inference('sup+', [status(thm)], ['36', '37'])).
% 2.55/2.72  thf('39', plain,
% 2.55/2.72      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B)) = (X0))),
% 2.55/2.72      inference('sup+', [status(thm)], ['35', '38'])).
% 2.55/2.72  thf('40', plain,
% 2.55/2.72      (((k3_xboole_0 @ sk_A @ sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.55/2.72      inference('sup+', [status(thm)], ['32', '39'])).
% 2.55/2.72  thf('41', plain,
% 2.55/2.72      (![X16 : $i, X17 : $i]:
% 2.55/2.72         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.55/2.72           = (k3_xboole_0 @ X16 @ X17))),
% 2.55/2.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.55/2.72  thf(t39_xboole_1, axiom,
% 2.55/2.72    (![A:$i,B:$i]:
% 2.55/2.72     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.55/2.72  thf('42', plain,
% 2.55/2.72      (![X6 : $i, X7 : $i]:
% 2.55/2.72         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 2.55/2.72           = (k2_xboole_0 @ X6 @ X7))),
% 2.55/2.72      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.55/2.72  thf('43', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.55/2.72           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 2.55/2.72      inference('sup+', [status(thm)], ['41', '42'])).
% 2.55/2.72  thf('44', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.55/2.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.55/2.72  thf('45', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.55/2.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.55/2.72  thf('46', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 2.55/2.72           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.55/2.72      inference('demod', [status(thm)], ['43', '44', '45'])).
% 2.55/2.72  thf('47', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 2.55/2.72      inference('demod', [status(thm)], ['12', '13'])).
% 2.55/2.72  thf('48', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 2.55/2.72           = (X1))),
% 2.55/2.72      inference('demod', [status(thm)], ['46', '47'])).
% 2.55/2.72  thf('49', plain,
% 2.55/2.72      (((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 2.55/2.72         (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 2.55/2.72      inference('sup+', [status(thm)], ['40', '48'])).
% 2.55/2.72  thf('50', plain,
% 2.55/2.72      (((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 2.55/2.72      inference('sup+', [status(thm)], ['33', '34'])).
% 2.55/2.72  thf('51', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 2.55/2.72      inference('sup-', [status(thm)], ['29', '30'])).
% 2.55/2.72  thf('52', plain,
% 2.55/2.72      (![X0 : $i]: ((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0) = (X0))),
% 2.55/2.72      inference('sup+', [status(thm)], ['50', '51'])).
% 2.55/2.72  thf('53', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 2.55/2.72      inference('demod', [status(thm)], ['49', '52'])).
% 2.55/2.72  thf(t42_xboole_1, axiom,
% 2.55/2.72    (![A:$i,B:$i,C:$i]:
% 2.55/2.72     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 2.55/2.72       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 2.55/2.72  thf('54', plain,
% 2.55/2.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.55/2.72         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X12) @ X11)
% 2.55/2.72           = (k2_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ 
% 2.55/2.72              (k4_xboole_0 @ X12 @ X11)))),
% 2.55/2.72      inference('cnf', [status(esa)], [t42_xboole_1])).
% 2.55/2.72  thf('55', plain,
% 2.55/2.72      (![X0 : $i]:
% 2.55/2.72         ((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ sk_A)
% 2.55/2.72           = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)))),
% 2.55/2.72      inference('sup+', [status(thm)], ['53', '54'])).
% 2.55/2.72  thf('56', plain,
% 2.55/2.72      (((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A))
% 2.55/2.72         != (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 2.55/2.72      inference('demod', [status(thm)], ['3', '55'])).
% 2.55/2.72  thf('57', plain, ($false), inference('simplify', [status(thm)], ['56'])).
% 2.55/2.72  
% 2.55/2.72  % SZS output end Refutation
% 2.55/2.72  
% 2.55/2.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
