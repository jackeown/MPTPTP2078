%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zqvfSvTXbL

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:17 EST 2020

% Result     : Theorem 30.83s
% Output     : Refutation 30.83s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 101 expanded)
%              Number of leaves         :   18 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  596 ( 978 expanded)
%              Number of equality atoms :   50 (  88 expanded)
%              Maximal formula depth    :   11 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t50_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
        = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('2',plain,(
    ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('4',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k2_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X3 @ X4 ) @ ( k4_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X3 @ X4 ) @ ( k4_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('37',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X3 @ X4 ) @ ( k4_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['35','38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['20','40'])).

thf('42',plain,(
    ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['2','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zqvfSvTXbL
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:21:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 30.83/31.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 30.83/31.08  % Solved by: fo/fo7.sh
% 30.83/31.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 30.83/31.08  % done 10917 iterations in 30.612s
% 30.83/31.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 30.83/31.08  % SZS output start Refutation
% 30.83/31.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 30.83/31.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 30.83/31.08  thf(sk_C_type, type, sk_C: $i).
% 30.83/31.08  thf(sk_B_type, type, sk_B: $i).
% 30.83/31.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 30.83/31.08  thf(sk_A_type, type, sk_A: $i).
% 30.83/31.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 30.83/31.08  thf(t50_xboole_1, conjecture,
% 30.83/31.08    (![A:$i,B:$i,C:$i]:
% 30.83/31.08     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 30.83/31.08       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 30.83/31.08  thf(zf_stmt_0, negated_conjecture,
% 30.83/31.08    (~( ![A:$i,B:$i,C:$i]:
% 30.83/31.08        ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 30.83/31.08          ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )),
% 30.83/31.08    inference('cnf.neg', [status(esa)], [t50_xboole_1])).
% 30.83/31.08  thf('0', plain,
% 30.83/31.08      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 30.83/31.08         != (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 30.83/31.08             (k3_xboole_0 @ sk_A @ sk_C)))),
% 30.83/31.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.83/31.08  thf(t49_xboole_1, axiom,
% 30.83/31.08    (![A:$i,B:$i,C:$i]:
% 30.83/31.08     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 30.83/31.08       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 30.83/31.08  thf('1', plain,
% 30.83/31.08      (![X20 : $i, X21 : $i, X22 : $i]:
% 30.83/31.08         ((k3_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 30.83/31.08           = (k4_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X22))),
% 30.83/31.08      inference('cnf', [status(esa)], [t49_xboole_1])).
% 30.83/31.08  thf('2', plain,
% 30.83/31.08      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 30.83/31.08         != (k3_xboole_0 @ sk_A @ 
% 30.83/31.08             (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_C))))),
% 30.83/31.08      inference('demod', [status(thm)], ['0', '1'])).
% 30.83/31.08  thf(t47_xboole_1, axiom,
% 30.83/31.08    (![A:$i,B:$i]:
% 30.83/31.08     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 30.83/31.08  thf('3', plain,
% 30.83/31.08      (![X18 : $i, X19 : $i]:
% 30.83/31.08         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 30.83/31.08           = (k4_xboole_0 @ X18 @ X19))),
% 30.83/31.08      inference('cnf', [status(esa)], [t47_xboole_1])).
% 30.83/31.08  thf('4', plain,
% 30.83/31.08      (![X20 : $i, X21 : $i, X22 : $i]:
% 30.83/31.08         ((k3_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 30.83/31.08           = (k4_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X22))),
% 30.83/31.08      inference('cnf', [status(esa)], [t49_xboole_1])).
% 30.83/31.08  thf('5', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.83/31.08         ((k3_xboole_0 @ X2 @ 
% 30.83/31.08           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 30.83/31.08           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 30.83/31.08      inference('sup+', [status(thm)], ['3', '4'])).
% 30.83/31.08  thf('6', plain,
% 30.83/31.08      (![X20 : $i, X21 : $i, X22 : $i]:
% 30.83/31.08         ((k3_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 30.83/31.08           = (k4_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X22))),
% 30.83/31.08      inference('cnf', [status(esa)], [t49_xboole_1])).
% 30.83/31.08  thf('7', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.83/31.08         ((k3_xboole_0 @ X2 @ 
% 30.83/31.08           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 30.83/31.08           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 30.83/31.08      inference('demod', [status(thm)], ['5', '6'])).
% 30.83/31.08  thf(t21_xboole_1, axiom,
% 30.83/31.08    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 30.83/31.08  thf('8', plain,
% 30.83/31.08      (![X8 : $i, X9 : $i]:
% 30.83/31.08         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (X8))),
% 30.83/31.08      inference('cnf', [status(esa)], [t21_xboole_1])).
% 30.83/31.08  thf(t23_xboole_1, axiom,
% 30.83/31.08    (![A:$i,B:$i,C:$i]:
% 30.83/31.08     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 30.83/31.08       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 30.83/31.08  thf('9', plain,
% 30.83/31.08      (![X10 : $i, X11 : $i, X12 : $i]:
% 30.83/31.08         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 30.83/31.08           = (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ 
% 30.83/31.08              (k3_xboole_0 @ X10 @ X12)))),
% 30.83/31.08      inference('cnf', [status(esa)], [t23_xboole_1])).
% 30.83/31.08  thf('10', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.83/31.08         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X1))
% 30.83/31.08           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 30.83/31.08      inference('sup+', [status(thm)], ['8', '9'])).
% 30.83/31.08  thf(t4_xboole_1, axiom,
% 30.83/31.08    (![A:$i,B:$i,C:$i]:
% 30.83/31.08     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 30.83/31.08       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 30.83/31.08  thf('11', plain,
% 30.83/31.08      (![X23 : $i, X24 : $i, X25 : $i]:
% 30.83/31.08         ((k2_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X25)
% 30.83/31.08           = (k2_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 30.83/31.08      inference('cnf', [status(esa)], [t4_xboole_1])).
% 30.83/31.08  thf('12', plain,
% 30.83/31.08      (![X8 : $i, X9 : $i]:
% 30.83/31.08         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (X8))),
% 30.83/31.08      inference('cnf', [status(esa)], [t21_xboole_1])).
% 30.83/31.08  thf('13', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i]:
% 30.83/31.08         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 30.83/31.08      inference('demod', [status(thm)], ['10', '11', '12'])).
% 30.83/31.08  thf(commutativity_k2_xboole_0, axiom,
% 30.83/31.08    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 30.83/31.08  thf('14', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 30.83/31.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 30.83/31.08  thf('15', plain,
% 30.83/31.08      (![X8 : $i, X9 : $i]:
% 30.83/31.08         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (X8))),
% 30.83/31.08      inference('cnf', [status(esa)], [t21_xboole_1])).
% 30.83/31.08  thf('16', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i]:
% 30.83/31.08         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 30.83/31.08      inference('sup+', [status(thm)], ['14', '15'])).
% 30.83/31.08  thf('17', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i]:
% 30.83/31.08         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 30.83/31.08           = (k3_xboole_0 @ X0 @ X1))),
% 30.83/31.08      inference('sup+', [status(thm)], ['13', '16'])).
% 30.83/31.08  thf('18', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.83/31.08         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X2)
% 30.83/31.08           = (k3_xboole_0 @ X2 @ 
% 30.83/31.08              (k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))))),
% 30.83/31.08      inference('sup+', [status(thm)], ['7', '17'])).
% 30.83/31.08  thf('19', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i]:
% 30.83/31.08         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 30.83/31.08           = (k3_xboole_0 @ X0 @ X1))),
% 30.83/31.08      inference('sup+', [status(thm)], ['13', '16'])).
% 30.83/31.08  thf('20', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.83/31.08         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 30.83/31.08           = (k3_xboole_0 @ X2 @ 
% 30.83/31.08              (k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))))),
% 30.83/31.08      inference('demod', [status(thm)], ['18', '19'])).
% 30.83/31.08  thf(t7_xboole_1, axiom,
% 30.83/31.08    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 30.83/31.08  thf('21', plain,
% 30.83/31.08      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 30.83/31.08      inference('cnf', [status(esa)], [t7_xboole_1])).
% 30.83/31.08  thf(t43_xboole_1, axiom,
% 30.83/31.08    (![A:$i,B:$i,C:$i]:
% 30.83/31.08     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 30.83/31.08       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 30.83/31.08  thf('22', plain,
% 30.83/31.08      (![X15 : $i, X16 : $i, X17 : $i]:
% 30.83/31.08         ((r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 30.83/31.08          | ~ (r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 30.83/31.08      inference('cnf', [status(esa)], [t43_xboole_1])).
% 30.83/31.08  thf('23', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 30.83/31.08      inference('sup-', [status(thm)], ['21', '22'])).
% 30.83/31.08  thf(t12_xboole_1, axiom,
% 30.83/31.08    (![A:$i,B:$i]:
% 30.83/31.08     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 30.83/31.08  thf('24', plain,
% 30.83/31.08      (![X6 : $i, X7 : $i]:
% 30.83/31.08         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 30.83/31.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 30.83/31.08  thf('25', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i]:
% 30.83/31.08         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 30.83/31.08      inference('sup-', [status(thm)], ['23', '24'])).
% 30.83/31.08  thf('26', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 30.83/31.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 30.83/31.08  thf('27', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i]:
% 30.83/31.08         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1)) = (X0))),
% 30.83/31.08      inference('sup+', [status(thm)], ['25', '26'])).
% 30.83/31.08  thf(l36_xboole_1, axiom,
% 30.83/31.08    (![A:$i,B:$i,C:$i]:
% 30.83/31.08     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 30.83/31.08       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 30.83/31.08  thf('28', plain,
% 30.83/31.08      (![X3 : $i, X4 : $i, X5 : $i]:
% 30.83/31.08         ((k4_xboole_0 @ X3 @ (k3_xboole_0 @ X4 @ X5))
% 30.83/31.08           = (k2_xboole_0 @ (k4_xboole_0 @ X3 @ X4) @ (k4_xboole_0 @ X3 @ X5)))),
% 30.83/31.08      inference('cnf', [status(esa)], [l36_xboole_1])).
% 30.83/31.08  thf('29', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i]:
% 30.83/31.08         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 30.83/31.08           = (k4_xboole_0 @ X1 @ X0))),
% 30.83/31.08      inference('sup+', [status(thm)], ['27', '28'])).
% 30.83/31.08  thf('30', plain,
% 30.83/31.08      (![X18 : $i, X19 : $i]:
% 30.83/31.08         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 30.83/31.08           = (k4_xboole_0 @ X18 @ X19))),
% 30.83/31.08      inference('cnf', [status(esa)], [t47_xboole_1])).
% 30.83/31.08  thf('31', plain,
% 30.83/31.08      (![X3 : $i, X4 : $i, X5 : $i]:
% 30.83/31.08         ((k4_xboole_0 @ X3 @ (k3_xboole_0 @ X4 @ X5))
% 30.83/31.08           = (k2_xboole_0 @ (k4_xboole_0 @ X3 @ X4) @ (k4_xboole_0 @ X3 @ X5)))),
% 30.83/31.08      inference('cnf', [status(esa)], [l36_xboole_1])).
% 30.83/31.08  thf('32', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.83/31.08         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 30.83/31.08           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2)))),
% 30.83/31.08      inference('sup+', [status(thm)], ['30', '31'])).
% 30.83/31.08  thf('33', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.83/31.08         ((k4_xboole_0 @ X1 @ 
% 30.83/31.08           (k3_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))
% 30.83/31.08           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2)))),
% 30.83/31.08      inference('sup+', [status(thm)], ['29', '32'])).
% 30.83/31.08  thf('34', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.83/31.08         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 30.83/31.08           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2)))),
% 30.83/31.08      inference('sup+', [status(thm)], ['30', '31'])).
% 30.83/31.08  thf('35', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.83/31.08         ((k4_xboole_0 @ X1 @ 
% 30.83/31.08           (k3_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))
% 30.83/31.08           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 30.83/31.08      inference('demod', [status(thm)], ['33', '34'])).
% 30.83/31.08  thf('36', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.83/31.08         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 30.83/31.08           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2)))),
% 30.83/31.08      inference('sup+', [status(thm)], ['30', '31'])).
% 30.83/31.08  thf('37', plain,
% 30.83/31.08      (![X3 : $i, X4 : $i, X5 : $i]:
% 30.83/31.08         ((k4_xboole_0 @ X3 @ (k3_xboole_0 @ X4 @ X5))
% 30.83/31.08           = (k2_xboole_0 @ (k4_xboole_0 @ X3 @ X4) @ (k4_xboole_0 @ X3 @ X5)))),
% 30.83/31.08      inference('cnf', [status(esa)], [l36_xboole_1])).
% 30.83/31.08  thf('38', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.83/31.08         ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 30.83/31.08           = (k4_xboole_0 @ X2 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 30.83/31.08      inference('sup+', [status(thm)], ['36', '37'])).
% 30.83/31.08  thf('39', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.83/31.08         ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 30.83/31.08           = (k4_xboole_0 @ X2 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 30.83/31.08      inference('sup+', [status(thm)], ['36', '37'])).
% 30.83/31.08  thf('40', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.83/31.08         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))
% 30.83/31.08           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2)))),
% 30.83/31.08      inference('demod', [status(thm)], ['35', '38', '39'])).
% 30.83/31.08  thf('41', plain,
% 30.83/31.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.83/31.08         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 30.83/31.08           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0))))),
% 30.83/31.08      inference('demod', [status(thm)], ['20', '40'])).
% 30.83/31.08  thf('42', plain,
% 30.83/31.08      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 30.83/31.08         != (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 30.83/31.08      inference('demod', [status(thm)], ['2', '41'])).
% 30.83/31.08  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 30.83/31.08  
% 30.83/31.08  % SZS output end Refutation
% 30.83/31.08  
% 30.83/31.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
