%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zvh0xGKR5o

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:09 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   58 (  91 expanded)
%              Number of leaves         :   17 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  444 ( 709 expanded)
%              Number of equality atoms :   38 (  68 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t47_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t47_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ ( k4_xboole_0 @ X15 @ X14 ) @ ( k4_xboole_0 @ X15 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','17'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','35','36'])).

thf('38',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','37'])).

thf('39',plain,(
    $false ),
    inference(simplify,[status(thm)],['38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zvh0xGKR5o
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:10:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.37/1.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.37/1.53  % Solved by: fo/fo7.sh
% 1.37/1.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.53  % done 2308 iterations in 1.084s
% 1.37/1.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.37/1.53  % SZS output start Refutation
% 1.37/1.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.37/1.53  thf(sk_B_type, type, sk_B: $i).
% 1.37/1.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.37/1.53  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.37/1.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.37/1.53  thf(t47_xboole_1, conjecture,
% 1.37/1.53    (![A:$i,B:$i]:
% 1.37/1.53     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.37/1.53  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.53    (~( ![A:$i,B:$i]:
% 1.37/1.53        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) =
% 1.37/1.53          ( k4_xboole_0 @ A @ B ) ) )),
% 1.37/1.53    inference('cnf.neg', [status(esa)], [t47_xboole_1])).
% 1.37/1.53  thf('0', plain,
% 1.37/1.53      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 1.37/1.53         != (k4_xboole_0 @ sk_A @ sk_B))),
% 1.37/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.53  thf(commutativity_k3_xboole_0, axiom,
% 1.37/1.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.37/1.53  thf('1', plain,
% 1.37/1.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.37/1.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.37/1.53  thf('2', plain,
% 1.37/1.53      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.37/1.53         != (k4_xboole_0 @ sk_A @ sk_B))),
% 1.37/1.53      inference('demod', [status(thm)], ['0', '1'])).
% 1.37/1.53  thf('3', plain,
% 1.37/1.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.37/1.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.37/1.53  thf(t39_xboole_1, axiom,
% 1.37/1.53    (![A:$i,B:$i]:
% 1.37/1.53     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.37/1.53  thf('4', plain,
% 1.37/1.53      (![X18 : $i, X19 : $i]:
% 1.37/1.53         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 1.37/1.53           = (k2_xboole_0 @ X18 @ X19))),
% 1.37/1.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.37/1.53  thf(t36_xboole_1, axiom,
% 1.37/1.53    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.37/1.53  thf('5', plain,
% 1.37/1.53      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 1.37/1.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.37/1.53  thf(t28_xboole_1, axiom,
% 1.37/1.53    (![A:$i,B:$i]:
% 1.37/1.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.37/1.53  thf('6', plain,
% 1.37/1.53      (![X11 : $i, X12 : $i]:
% 1.37/1.53         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 1.37/1.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.37/1.53  thf('7', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i]:
% 1.37/1.53         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.37/1.53           = (k4_xboole_0 @ X0 @ X1))),
% 1.37/1.53      inference('sup-', [status(thm)], ['5', '6'])).
% 1.37/1.53  thf('8', plain,
% 1.37/1.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.37/1.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.37/1.53  thf('9', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i]:
% 1.37/1.53         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.37/1.53           = (k4_xboole_0 @ X0 @ X1))),
% 1.37/1.53      inference('demod', [status(thm)], ['7', '8'])).
% 1.37/1.53  thf(t23_xboole_1, axiom,
% 1.37/1.53    (![A:$i,B:$i,C:$i]:
% 1.37/1.53     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.37/1.53       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.37/1.53  thf('10', plain,
% 1.37/1.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.37/1.53         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10))
% 1.37/1.53           = (k2_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X10)))),
% 1.37/1.53      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.37/1.53  thf('11', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.53         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 1.37/1.53           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.37/1.53      inference('sup+', [status(thm)], ['9', '10'])).
% 1.37/1.53  thf('12', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i]:
% 1.37/1.53         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.37/1.53           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 1.37/1.53      inference('sup+', [status(thm)], ['4', '11'])).
% 1.37/1.53  thf(commutativity_k2_xboole_0, axiom,
% 1.37/1.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.37/1.53  thf('13', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.37/1.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.37/1.53  thf(t21_xboole_1, axiom,
% 1.37/1.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.37/1.53  thf('14', plain,
% 1.37/1.53      (![X6 : $i, X7 : $i]:
% 1.37/1.53         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 1.37/1.53      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.37/1.53  thf('15', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i]:
% 1.37/1.53         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 1.37/1.53      inference('sup+', [status(thm)], ['13', '14'])).
% 1.37/1.53  thf('16', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.37/1.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.37/1.53  thf('17', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i]:
% 1.37/1.53         ((X0)
% 1.37/1.53           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 1.37/1.53      inference('demod', [status(thm)], ['12', '15', '16'])).
% 1.37/1.53  thf('18', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i]:
% 1.37/1.53         ((X0)
% 1.37/1.53           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.37/1.53      inference('sup+', [status(thm)], ['3', '17'])).
% 1.37/1.53  thf('19', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.37/1.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.37/1.53  thf('20', plain,
% 1.37/1.53      (![X6 : $i, X7 : $i]:
% 1.37/1.53         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 1.37/1.53      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.37/1.53  thf(t17_xboole_1, axiom,
% 1.37/1.53    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.37/1.53  thf('21', plain,
% 1.37/1.53      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 1.37/1.53      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.37/1.53  thf('22', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.37/1.53      inference('sup+', [status(thm)], ['20', '21'])).
% 1.37/1.53  thf(t43_xboole_1, axiom,
% 1.37/1.53    (![A:$i,B:$i,C:$i]:
% 1.37/1.53     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.37/1.53       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.37/1.53  thf('23', plain,
% 1.37/1.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.37/1.53         ((r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 1.37/1.53          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 1.37/1.53      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.37/1.53  thf('24', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i]:
% 1.37/1.53         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 1.37/1.53      inference('sup-', [status(thm)], ['22', '23'])).
% 1.37/1.53  thf('25', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i]:
% 1.37/1.53         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) @ X1)),
% 1.37/1.53      inference('sup+', [status(thm)], ['19', '24'])).
% 1.37/1.53  thf('26', plain,
% 1.37/1.53      (![X11 : $i, X12 : $i]:
% 1.37/1.53         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 1.37/1.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.37/1.53  thf('27', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i]:
% 1.37/1.53         ((k3_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1) @ X0)
% 1.37/1.53           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1))),
% 1.37/1.53      inference('sup-', [status(thm)], ['25', '26'])).
% 1.37/1.53  thf('28', plain,
% 1.37/1.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.37/1.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.37/1.53  thf('29', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i]:
% 1.37/1.53         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1))
% 1.37/1.53           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1))),
% 1.37/1.53      inference('demod', [status(thm)], ['27', '28'])).
% 1.37/1.53  thf('30', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i]:
% 1.37/1.53         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 1.37/1.53           (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.37/1.53           = (k4_xboole_0 @ 
% 1.37/1.53              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.37/1.53              (k3_xboole_0 @ X1 @ X0)))),
% 1.37/1.53      inference('sup+', [status(thm)], ['18', '29'])).
% 1.37/1.53  thf('31', plain,
% 1.37/1.53      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 1.37/1.53      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.37/1.53  thf(t34_xboole_1, axiom,
% 1.37/1.53    (![A:$i,B:$i,C:$i]:
% 1.37/1.53     ( ( r1_tarski @ A @ B ) =>
% 1.37/1.53       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 1.37/1.53  thf('32', plain,
% 1.37/1.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.37/1.53         (~ (r1_tarski @ X13 @ X14)
% 1.37/1.53          | (r1_tarski @ (k4_xboole_0 @ X15 @ X14) @ (k4_xboole_0 @ X15 @ X13)))),
% 1.37/1.53      inference('cnf', [status(esa)], [t34_xboole_1])).
% 1.37/1.53  thf('33', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.53         (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ 
% 1.37/1.53          (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.37/1.53      inference('sup-', [status(thm)], ['31', '32'])).
% 1.37/1.53  thf('34', plain,
% 1.37/1.53      (![X11 : $i, X12 : $i]:
% 1.37/1.53         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 1.37/1.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.37/1.53  thf('35', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.53         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 1.37/1.53           (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 1.37/1.53           = (k4_xboole_0 @ X2 @ X1))),
% 1.37/1.53      inference('sup-', [status(thm)], ['33', '34'])).
% 1.37/1.53  thf('36', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i]:
% 1.37/1.53         ((X0)
% 1.37/1.53           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.37/1.53      inference('sup+', [status(thm)], ['3', '17'])).
% 1.37/1.53  thf('37', plain,
% 1.37/1.53      (![X0 : $i, X1 : $i]:
% 1.37/1.53         ((k4_xboole_0 @ X0 @ X1)
% 1.37/1.53           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.37/1.53      inference('demod', [status(thm)], ['30', '35', '36'])).
% 1.37/1.53  thf('38', plain,
% 1.37/1.53      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 1.37/1.53      inference('demod', [status(thm)], ['2', '37'])).
% 1.37/1.53  thf('39', plain, ($false), inference('simplify', [status(thm)], ['38'])).
% 1.37/1.53  
% 1.37/1.53  % SZS output end Refutation
% 1.37/1.53  
% 1.37/1.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
