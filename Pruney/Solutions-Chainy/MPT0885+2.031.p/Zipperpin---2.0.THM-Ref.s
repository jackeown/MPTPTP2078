%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dHeIceeraD

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:31 EST 2020

% Result     : Theorem 3.06s
% Output     : Refutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   57 (  82 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  750 (1174 expanded)
%              Number of equality atoms :   44 (  77 expanded)
%              Maximal formula depth    :   15 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t45_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) )
        = ( k2_enumset1 @ ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_E ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t104_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X3 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('2',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_E ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_tarski @ ( k4_tarski @ X13 @ X14 ) @ ( k4_tarski @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_mcart_1 @ X17 @ X18 @ X19 )
      = ( k4_tarski @ ( k4_tarski @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('5',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X13 @ X14 ) @ ( k1_tarski @ X16 ) )
      = ( k2_tarski @ ( k4_tarski @ X13 @ X16 ) @ ( k4_tarski @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ X3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_tarski @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_zfmisc_1 @ X20 @ X21 @ X22 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_mcart_1 @ X17 @ X18 @ X19 )
      = ( k4_tarski @ ( k4_tarski @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) @ ( k3_mcart_1 @ X2 @ X0 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t45_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ ( k3_mcart_1 @ X3 @ X2 @ X0 ) @ ( k3_mcart_1 @ X3 @ X1 @ X0 ) @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ ( k1_tarski @ X3 ) @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X3 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X2 ) @ X1 @ ( k3_mcart_1 @ X5 @ X3 @ X2 ) @ X0 )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ ( k1_tarski @ X5 ) @ ( k2_tarski @ X4 @ X3 ) @ ( k1_tarski @ X2 ) ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) @ ( k3_mcart_1 @ X2 @ X0 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('16',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_xboole_0 @ ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D ) ) @ ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['2','14','15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_tarski @ ( k4_tarski @ X13 @ X14 ) @ ( k4_tarski @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(t146_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X9 @ X12 ) @ ( k2_tarski @ X10 @ X11 ) )
      = ( k2_enumset1 @ ( k4_tarski @ X9 @ X10 ) @ ( k4_tarski @ X9 @ X11 ) @ ( k4_tarski @ X12 @ X10 ) @ ( k4_tarski @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t146_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X3 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ ( k4_tarski @ X3 @ X1 ) @ ( k4_tarski @ X2 @ X1 ) @ ( k4_tarski @ X3 @ X0 ) @ ( k4_tarski @ X2 @ X0 ) )
      = ( k2_zfmisc_1 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X13 @ X14 ) @ ( k1_tarski @ X16 ) )
      = ( k2_tarski @ ( k4_tarski @ X13 @ X16 ) @ ( k4_tarski @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_enumset1 @ ( k4_tarski @ X2 @ X0 ) @ ( k4_tarski @ X1 @ X0 ) @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_tarski @ X3 @ X2 ) @ ( k1_tarski @ X1 ) ) @ ( k2_tarski @ ( k4_tarski @ X3 @ X0 ) @ ( k4_tarski @ X2 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X13 @ X14 ) @ ( k1_tarski @ X16 ) )
      = ( k2_tarski @ ( k4_tarski @ X13 @ X16 ) @ ( k4_tarski @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_tarski @ X3 @ X2 ) @ ( k1_tarski @ X1 ) ) @ ( k2_zfmisc_1 @ ( k2_tarski @ X3 @ X2 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ ( k4_tarski @ X2 @ X0 ) ) @ ( k2_tarski @ X4 @ X3 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_tarski @ X4 ) ) @ ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ ( k4_tarski @ X2 @ X0 ) ) @ ( k1_tarski @ X3 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','26'])).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_tarski @ ( k4_tarski @ X13 @ X14 ) @ ( k4_tarski @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_zfmisc_1 @ X20 @ X21 @ X22 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_zfmisc_1 @ X20 @ X21 @ X22 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_tarski @ ( k4_tarski @ X13 @ X14 ) @ ( k4_tarski @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('32',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_zfmisc_1 @ X20 @ X21 @ X22 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) @ ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28','29','30','31','32'])).

thf('34',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['16','33'])).

thf('35',plain,(
    $false ),
    inference(simplify,[status(thm)],['34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dHeIceeraD
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 13:20:57 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 3.06/3.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.06/3.24  % Solved by: fo/fo7.sh
% 3.06/3.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.06/3.24  % done 1575 iterations in 2.809s
% 3.06/3.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.06/3.24  % SZS output start Refutation
% 3.06/3.24  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.06/3.24  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.06/3.24  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.06/3.24  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 3.06/3.24  thf(sk_B_type, type, sk_B: $i).
% 3.06/3.24  thf(sk_A_type, type, sk_A: $i).
% 3.06/3.24  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 3.06/3.24  thf(sk_E_type, type, sk_E: $i).
% 3.06/3.24  thf(sk_C_type, type, sk_C: $i).
% 3.06/3.24  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.06/3.24  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 3.06/3.24  thf(sk_D_type, type, sk_D: $i).
% 3.06/3.24  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.06/3.24  thf(t45_mcart_1, conjecture,
% 3.06/3.24    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 3.06/3.24     ( ( k3_zfmisc_1 @
% 3.06/3.24         ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) =
% 3.06/3.24       ( k2_enumset1 @
% 3.06/3.24         ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ 
% 3.06/3.24         ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ))).
% 3.06/3.24  thf(zf_stmt_0, negated_conjecture,
% 3.06/3.24    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 3.06/3.24        ( ( k3_zfmisc_1 @
% 3.06/3.24            ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) =
% 3.06/3.24          ( k2_enumset1 @
% 3.06/3.24            ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ 
% 3.06/3.24            ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) )),
% 3.06/3.24    inference('cnf.neg', [status(esa)], [t45_mcart_1])).
% 3.06/3.24  thf('0', plain,
% 3.06/3.24      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 3.06/3.24         (k2_tarski @ sk_D @ sk_E))
% 3.06/3.24         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_D) @ 
% 3.06/3.24             (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.06/3.24             (k3_mcart_1 @ sk_A @ sk_B @ sk_E) @ 
% 3.06/3.24             (k3_mcart_1 @ sk_A @ sk_C @ sk_E)))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf(t104_enumset1, axiom,
% 3.06/3.24    (![A:$i,B:$i,C:$i,D:$i]:
% 3.06/3.24     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 3.06/3.24  thf('1', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.06/3.24         ((k2_enumset1 @ X0 @ X2 @ X1 @ X3) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 3.06/3.24      inference('cnf', [status(esa)], [t104_enumset1])).
% 3.06/3.24  thf('2', plain,
% 3.06/3.24      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 3.06/3.24         (k2_tarski @ sk_D @ sk_E))
% 3.06/3.24         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_D) @ 
% 3.06/3.24             (k3_mcart_1 @ sk_A @ sk_B @ sk_E) @ 
% 3.06/3.24             (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.06/3.24             (k3_mcart_1 @ sk_A @ sk_C @ sk_E)))),
% 3.06/3.24      inference('demod', [status(thm)], ['0', '1'])).
% 3.06/3.24  thf(t36_zfmisc_1, axiom,
% 3.06/3.24    (![A:$i,B:$i,C:$i]:
% 3.06/3.24     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 3.06/3.24         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 3.06/3.24       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 3.06/3.24         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 3.06/3.24  thf('3', plain,
% 3.06/3.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.06/3.24         ((k2_zfmisc_1 @ (k1_tarski @ X13) @ (k2_tarski @ X14 @ X15))
% 3.06/3.24           = (k2_tarski @ (k4_tarski @ X13 @ X14) @ (k4_tarski @ X13 @ X15)))),
% 3.06/3.24      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 3.06/3.24  thf(d3_mcart_1, axiom,
% 3.06/3.24    (![A:$i,B:$i,C:$i]:
% 3.06/3.24     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 3.06/3.24  thf('4', plain,
% 3.06/3.24      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.06/3.24         ((k3_mcart_1 @ X17 @ X18 @ X19)
% 3.06/3.24           = (k4_tarski @ (k4_tarski @ X17 @ X18) @ X19))),
% 3.06/3.24      inference('cnf', [status(esa)], [d3_mcart_1])).
% 3.06/3.24  thf('5', plain,
% 3.06/3.24      (![X13 : $i, X14 : $i, X16 : $i]:
% 3.06/3.24         ((k2_zfmisc_1 @ (k2_tarski @ X13 @ X14) @ (k1_tarski @ X16))
% 3.06/3.24           = (k2_tarski @ (k4_tarski @ X13 @ X16) @ (k4_tarski @ X14 @ X16)))),
% 3.06/3.24      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 3.06/3.24  thf('6', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.06/3.24         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X3) @ 
% 3.06/3.24           (k1_tarski @ X0))
% 3.06/3.24           = (k2_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ (k4_tarski @ X3 @ X0)))),
% 3.06/3.24      inference('sup+', [status(thm)], ['4', '5'])).
% 3.06/3.24  thf('7', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.06/3.24         ((k2_zfmisc_1 @ 
% 3.06/3.24           (k2_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)) @ 
% 3.06/3.24           (k1_tarski @ X3))
% 3.06/3.24           = (k2_tarski @ (k3_mcart_1 @ X2 @ X1 @ X3) @ 
% 3.06/3.24              (k4_tarski @ (k4_tarski @ X2 @ X0) @ X3)))),
% 3.06/3.24      inference('sup+', [status(thm)], ['3', '6'])).
% 3.06/3.24  thf(d3_zfmisc_1, axiom,
% 3.06/3.24    (![A:$i,B:$i,C:$i]:
% 3.06/3.24     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 3.06/3.24       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 3.06/3.24  thf('8', plain,
% 3.06/3.24      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.06/3.24         ((k3_zfmisc_1 @ X20 @ X21 @ X22)
% 3.06/3.24           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21) @ X22))),
% 3.06/3.24      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 3.06/3.24  thf('9', plain,
% 3.06/3.24      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.06/3.24         ((k3_mcart_1 @ X17 @ X18 @ X19)
% 3.06/3.24           = (k4_tarski @ (k4_tarski @ X17 @ X18) @ X19))),
% 3.06/3.24      inference('cnf', [status(esa)], [d3_mcart_1])).
% 3.06/3.24  thf('10', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.06/3.24         ((k3_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0) @ 
% 3.06/3.24           (k1_tarski @ X3))
% 3.06/3.24           = (k2_tarski @ (k3_mcart_1 @ X2 @ X1 @ X3) @ 
% 3.06/3.24              (k3_mcart_1 @ X2 @ X0 @ X3)))),
% 3.06/3.24      inference('demod', [status(thm)], ['7', '8', '9'])).
% 3.06/3.24  thf(t45_enumset1, axiom,
% 3.06/3.24    (![A:$i,B:$i,C:$i,D:$i]:
% 3.06/3.24     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 3.06/3.24       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 3.06/3.24  thf('11', plain,
% 3.06/3.24      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 3.06/3.24         ((k2_enumset1 @ X4 @ X5 @ X6 @ X7)
% 3.06/3.24           = (k2_xboole_0 @ (k2_tarski @ X4 @ X5) @ (k2_tarski @ X6 @ X7)))),
% 3.06/3.24      inference('cnf', [status(esa)], [t45_enumset1])).
% 3.06/3.24  thf('12', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 3.06/3.24         ((k2_enumset1 @ (k3_mcart_1 @ X3 @ X2 @ X0) @ 
% 3.06/3.24           (k3_mcart_1 @ X3 @ X1 @ X0) @ X5 @ X4)
% 3.06/3.24           = (k2_xboole_0 @ 
% 3.06/3.24              (k3_zfmisc_1 @ (k1_tarski @ X3) @ (k2_tarski @ X2 @ X1) @ 
% 3.06/3.24               (k1_tarski @ X0)) @ 
% 3.06/3.24              (k2_tarski @ X5 @ X4)))),
% 3.06/3.24      inference('sup+', [status(thm)], ['10', '11'])).
% 3.06/3.24  thf('13', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.06/3.24         ((k2_enumset1 @ X0 @ X2 @ X1 @ X3) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 3.06/3.24      inference('cnf', [status(esa)], [t104_enumset1])).
% 3.06/3.24  thf('14', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 3.06/3.24         ((k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X2) @ X1 @ 
% 3.06/3.24           (k3_mcart_1 @ X5 @ X3 @ X2) @ X0)
% 3.06/3.24           = (k2_xboole_0 @ 
% 3.06/3.24              (k3_zfmisc_1 @ (k1_tarski @ X5) @ (k2_tarski @ X4 @ X3) @ 
% 3.06/3.24               (k1_tarski @ X2)) @ 
% 3.06/3.24              (k2_tarski @ X1 @ X0)))),
% 3.06/3.24      inference('sup+', [status(thm)], ['12', '13'])).
% 3.06/3.24  thf('15', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.06/3.24         ((k3_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0) @ 
% 3.06/3.24           (k1_tarski @ X3))
% 3.06/3.24           = (k2_tarski @ (k3_mcart_1 @ X2 @ X1 @ X3) @ 
% 3.06/3.24              (k3_mcart_1 @ X2 @ X0 @ X3)))),
% 3.06/3.24      inference('demod', [status(thm)], ['7', '8', '9'])).
% 3.06/3.24  thf('16', plain,
% 3.06/3.24      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 3.06/3.24         (k2_tarski @ sk_D @ sk_E))
% 3.06/3.24         != (k2_xboole_0 @ 
% 3.06/3.24             (k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 3.06/3.24              (k1_tarski @ sk_D)) @ 
% 3.06/3.24             (k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 3.06/3.24              (k1_tarski @ sk_E))))),
% 3.06/3.24      inference('demod', [status(thm)], ['2', '14', '15'])).
% 3.06/3.24  thf('17', plain,
% 3.06/3.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.06/3.24         ((k2_zfmisc_1 @ (k1_tarski @ X13) @ (k2_tarski @ X14 @ X15))
% 3.06/3.24           = (k2_tarski @ (k4_tarski @ X13 @ X14) @ (k4_tarski @ X13 @ X15)))),
% 3.06/3.24      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 3.06/3.24  thf(t146_zfmisc_1, axiom,
% 3.06/3.24    (![A:$i,B:$i,C:$i,D:$i]:
% 3.06/3.24     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 3.06/3.24       ( k2_enumset1 @
% 3.06/3.24         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 3.06/3.24         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 3.06/3.24  thf('18', plain,
% 3.06/3.24      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 3.06/3.24         ((k2_zfmisc_1 @ (k2_tarski @ X9 @ X12) @ (k2_tarski @ X10 @ X11))
% 3.06/3.24           = (k2_enumset1 @ (k4_tarski @ X9 @ X10) @ (k4_tarski @ X9 @ X11) @ 
% 3.06/3.24              (k4_tarski @ X12 @ X10) @ (k4_tarski @ X12 @ X11)))),
% 3.06/3.24      inference('cnf', [status(esa)], [t146_zfmisc_1])).
% 3.06/3.24  thf('19', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.06/3.24         ((k2_enumset1 @ X0 @ X2 @ X1 @ X3) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 3.06/3.24      inference('cnf', [status(esa)], [t104_enumset1])).
% 3.06/3.24  thf('20', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.06/3.24         ((k2_enumset1 @ (k4_tarski @ X3 @ X1) @ (k4_tarski @ X2 @ X1) @ 
% 3.06/3.24           (k4_tarski @ X3 @ X0) @ (k4_tarski @ X2 @ X0))
% 3.06/3.24           = (k2_zfmisc_1 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 3.06/3.24      inference('sup+', [status(thm)], ['18', '19'])).
% 3.06/3.24  thf('21', plain,
% 3.06/3.24      (![X13 : $i, X14 : $i, X16 : $i]:
% 3.06/3.24         ((k2_zfmisc_1 @ (k2_tarski @ X13 @ X14) @ (k1_tarski @ X16))
% 3.06/3.24           = (k2_tarski @ (k4_tarski @ X13 @ X16) @ (k4_tarski @ X14 @ X16)))),
% 3.06/3.24      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 3.06/3.24  thf('22', plain,
% 3.06/3.24      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 3.06/3.24         ((k2_enumset1 @ X4 @ X5 @ X6 @ X7)
% 3.06/3.24           = (k2_xboole_0 @ (k2_tarski @ X4 @ X5) @ (k2_tarski @ X6 @ X7)))),
% 3.06/3.24      inference('cnf', [status(esa)], [t45_enumset1])).
% 3.06/3.24  thf('23', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.06/3.24         ((k2_enumset1 @ (k4_tarski @ X2 @ X0) @ (k4_tarski @ X1 @ X0) @ X4 @ 
% 3.06/3.24           X3)
% 3.06/3.24           = (k2_xboole_0 @ 
% 3.06/3.24              (k2_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)) @ 
% 3.06/3.24              (k2_tarski @ X4 @ X3)))),
% 3.06/3.24      inference('sup+', [status(thm)], ['21', '22'])).
% 3.06/3.24  thf('24', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.06/3.24         ((k2_zfmisc_1 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 3.06/3.24           = (k2_xboole_0 @ 
% 3.06/3.24              (k2_zfmisc_1 @ (k2_tarski @ X3 @ X2) @ (k1_tarski @ X1)) @ 
% 3.06/3.24              (k2_tarski @ (k4_tarski @ X3 @ X0) @ (k4_tarski @ X2 @ X0))))),
% 3.06/3.24      inference('sup+', [status(thm)], ['20', '23'])).
% 3.06/3.24  thf('25', plain,
% 3.06/3.24      (![X13 : $i, X14 : $i, X16 : $i]:
% 3.06/3.24         ((k2_zfmisc_1 @ (k2_tarski @ X13 @ X14) @ (k1_tarski @ X16))
% 3.06/3.24           = (k2_tarski @ (k4_tarski @ X13 @ X16) @ (k4_tarski @ X14 @ X16)))),
% 3.06/3.24      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 3.06/3.24  thf('26', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.06/3.24         ((k2_zfmisc_1 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 3.06/3.24           = (k2_xboole_0 @ 
% 3.06/3.24              (k2_zfmisc_1 @ (k2_tarski @ X3 @ X2) @ (k1_tarski @ X1)) @ 
% 3.06/3.24              (k2_zfmisc_1 @ (k2_tarski @ X3 @ X2) @ (k1_tarski @ X0))))),
% 3.06/3.24      inference('demod', [status(thm)], ['24', '25'])).
% 3.06/3.24  thf('27', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.06/3.24         ((k2_zfmisc_1 @ 
% 3.06/3.24           (k2_tarski @ (k4_tarski @ X2 @ X1) @ (k4_tarski @ X2 @ X0)) @ 
% 3.06/3.24           (k2_tarski @ X4 @ X3))
% 3.06/3.24           = (k2_xboole_0 @ 
% 3.06/3.24              (k2_zfmisc_1 @ 
% 3.06/3.24               (k2_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)) @ 
% 3.06/3.24               (k1_tarski @ X4)) @ 
% 3.06/3.24              (k2_zfmisc_1 @ 
% 3.06/3.24               (k2_tarski @ (k4_tarski @ X2 @ X1) @ (k4_tarski @ X2 @ X0)) @ 
% 3.06/3.24               (k1_tarski @ X3))))),
% 3.06/3.24      inference('sup+', [status(thm)], ['17', '26'])).
% 3.06/3.24  thf('28', plain,
% 3.06/3.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.06/3.24         ((k2_zfmisc_1 @ (k1_tarski @ X13) @ (k2_tarski @ X14 @ X15))
% 3.06/3.24           = (k2_tarski @ (k4_tarski @ X13 @ X14) @ (k4_tarski @ X13 @ X15)))),
% 3.06/3.24      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 3.06/3.24  thf('29', plain,
% 3.06/3.24      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.06/3.24         ((k3_zfmisc_1 @ X20 @ X21 @ X22)
% 3.06/3.24           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21) @ X22))),
% 3.06/3.24      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 3.06/3.24  thf('30', plain,
% 3.06/3.24      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.06/3.24         ((k3_zfmisc_1 @ X20 @ X21 @ X22)
% 3.06/3.24           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21) @ X22))),
% 3.06/3.24      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 3.06/3.24  thf('31', plain,
% 3.06/3.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.06/3.24         ((k2_zfmisc_1 @ (k1_tarski @ X13) @ (k2_tarski @ X14 @ X15))
% 3.06/3.24           = (k2_tarski @ (k4_tarski @ X13 @ X14) @ (k4_tarski @ X13 @ X15)))),
% 3.06/3.24      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 3.06/3.24  thf('32', plain,
% 3.06/3.24      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.06/3.24         ((k3_zfmisc_1 @ X20 @ X21 @ X22)
% 3.06/3.24           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21) @ X22))),
% 3.06/3.24      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 3.06/3.24  thf('33', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.06/3.24         ((k3_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0) @ 
% 3.06/3.24           (k2_tarski @ X4 @ X3))
% 3.06/3.24           = (k2_xboole_0 @ 
% 3.06/3.24              (k3_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0) @ 
% 3.06/3.24               (k1_tarski @ X4)) @ 
% 3.06/3.24              (k3_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0) @ 
% 3.06/3.24               (k1_tarski @ X3))))),
% 3.06/3.24      inference('demod', [status(thm)], ['27', '28', '29', '30', '31', '32'])).
% 3.06/3.24  thf('34', plain,
% 3.06/3.24      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 3.06/3.24         (k2_tarski @ sk_D @ sk_E))
% 3.06/3.24         != (k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 3.06/3.24             (k2_tarski @ sk_D @ sk_E)))),
% 3.06/3.24      inference('demod', [status(thm)], ['16', '33'])).
% 3.06/3.24  thf('35', plain, ($false), inference('simplify', [status(thm)], ['34'])).
% 3.06/3.24  
% 3.06/3.24  % SZS output end Refutation
% 3.06/3.24  
% 3.06/3.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
