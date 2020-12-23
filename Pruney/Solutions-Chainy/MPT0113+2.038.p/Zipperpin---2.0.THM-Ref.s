%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LcpFCv4f8X

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:33 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 117 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :   19
%              Number of atoms          :  458 ( 792 expanded)
%              Number of equality atoms :   43 (  65 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['2','5'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['23','28'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','42','43'])).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','48'])).

thf('50',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('51',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['11','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LcpFCv4f8X
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.13/1.37  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.13/1.37  % Solved by: fo/fo7.sh
% 1.13/1.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.13/1.37  % done 2995 iterations in 0.921s
% 1.13/1.37  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.13/1.37  % SZS output start Refutation
% 1.13/1.37  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.13/1.37  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.13/1.37  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.13/1.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.13/1.37  thf(sk_B_type, type, sk_B: $i).
% 1.13/1.37  thf(sk_C_type, type, sk_C: $i).
% 1.13/1.37  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.13/1.37  thf(sk_A_type, type, sk_A: $i).
% 1.13/1.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.13/1.37  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.13/1.37  thf(t106_xboole_1, conjecture,
% 1.13/1.37    (![A:$i,B:$i,C:$i]:
% 1.13/1.37     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.13/1.37       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 1.13/1.37  thf(zf_stmt_0, negated_conjecture,
% 1.13/1.37    (~( ![A:$i,B:$i,C:$i]:
% 1.13/1.37        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.13/1.37          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 1.13/1.37    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 1.13/1.37  thf('0', plain,
% 1.13/1.37      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 1.13/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.37  thf('1', plain,
% 1.13/1.37      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 1.13/1.37      inference('split', [status(esa)], ['0'])).
% 1.13/1.37  thf(t79_xboole_1, axiom,
% 1.13/1.37    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.13/1.37  thf('2', plain,
% 1.13/1.37      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 1.13/1.37      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.13/1.37  thf('3', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.13/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.37  thf(t63_xboole_1, axiom,
% 1.13/1.37    (![A:$i,B:$i,C:$i]:
% 1.13/1.37     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.13/1.37       ( r1_xboole_0 @ A @ C ) ))).
% 1.13/1.37  thf('4', plain,
% 1.13/1.37      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.13/1.37         (~ (r1_tarski @ X15 @ X16)
% 1.13/1.37          | ~ (r1_xboole_0 @ X16 @ X17)
% 1.13/1.37          | (r1_xboole_0 @ X15 @ X17))),
% 1.13/1.37      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.13/1.37  thf('5', plain,
% 1.13/1.37      (![X0 : $i]:
% 1.13/1.37         ((r1_xboole_0 @ sk_A @ X0)
% 1.13/1.37          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))),
% 1.13/1.37      inference('sup-', [status(thm)], ['3', '4'])).
% 1.13/1.37  thf('6', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 1.13/1.37      inference('sup-', [status(thm)], ['2', '5'])).
% 1.13/1.37  thf('7', plain,
% 1.13/1.37      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 1.13/1.37      inference('split', [status(esa)], ['0'])).
% 1.13/1.37  thf('8', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 1.13/1.37      inference('sup-', [status(thm)], ['6', '7'])).
% 1.13/1.37  thf('9', plain,
% 1.13/1.37      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 1.13/1.37      inference('split', [status(esa)], ['0'])).
% 1.13/1.37  thf('10', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 1.13/1.37      inference('sat_resolution*', [status(thm)], ['8', '9'])).
% 1.13/1.37  thf('11', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 1.13/1.37      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 1.13/1.37  thf('12', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.13/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.37  thf(l32_xboole_1, axiom,
% 1.13/1.37    (![A:$i,B:$i]:
% 1.13/1.37     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.13/1.37  thf('13', plain,
% 1.13/1.37      (![X5 : $i, X7 : $i]:
% 1.13/1.37         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.13/1.37      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.13/1.37  thf('14', plain,
% 1.13/1.37      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 1.13/1.37      inference('sup-', [status(thm)], ['12', '13'])).
% 1.13/1.37  thf('15', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 1.13/1.37      inference('sup-', [status(thm)], ['2', '5'])).
% 1.13/1.37  thf(d7_xboole_0, axiom,
% 1.13/1.37    (![A:$i,B:$i]:
% 1.13/1.37     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.13/1.37       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.13/1.37  thf('16', plain,
% 1.13/1.37      (![X2 : $i, X3 : $i]:
% 1.13/1.37         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.13/1.37      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.13/1.37  thf('17', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 1.13/1.37      inference('sup-', [status(thm)], ['15', '16'])).
% 1.13/1.37  thf(commutativity_k3_xboole_0, axiom,
% 1.13/1.37    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.13/1.37  thf('18', plain,
% 1.13/1.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.13/1.37  thf('19', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 1.13/1.37      inference('demod', [status(thm)], ['17', '18'])).
% 1.13/1.37  thf('20', plain,
% 1.13/1.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.13/1.37  thf(t100_xboole_1, axiom,
% 1.13/1.37    (![A:$i,B:$i]:
% 1.13/1.37     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.13/1.37  thf('21', plain,
% 1.13/1.37      (![X8 : $i, X9 : $i]:
% 1.13/1.37         ((k4_xboole_0 @ X8 @ X9)
% 1.13/1.37           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.13/1.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.13/1.37  thf('22', plain,
% 1.13/1.37      (![X0 : $i, X1 : $i]:
% 1.13/1.37         ((k4_xboole_0 @ X0 @ X1)
% 1.13/1.37           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.13/1.37      inference('sup+', [status(thm)], ['20', '21'])).
% 1.13/1.37  thf('23', plain,
% 1.13/1.37      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 1.13/1.37      inference('sup+', [status(thm)], ['19', '22'])).
% 1.13/1.37  thf(t4_boole, axiom,
% 1.13/1.37    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.13/1.37  thf('24', plain,
% 1.13/1.37      (![X14 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 1.13/1.37      inference('cnf', [status(esa)], [t4_boole])).
% 1.13/1.37  thf(t98_xboole_1, axiom,
% 1.13/1.37    (![A:$i,B:$i]:
% 1.13/1.37     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.13/1.37  thf('25', plain,
% 1.13/1.37      (![X20 : $i, X21 : $i]:
% 1.13/1.37         ((k2_xboole_0 @ X20 @ X21)
% 1.13/1.37           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 1.13/1.37      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.13/1.37  thf('26', plain,
% 1.13/1.37      (![X0 : $i]:
% 1.13/1.37         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.13/1.37      inference('sup+', [status(thm)], ['24', '25'])).
% 1.13/1.37  thf(t1_boole, axiom,
% 1.13/1.37    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.13/1.37  thf('27', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.13/1.37      inference('cnf', [status(esa)], [t1_boole])).
% 1.13/1.37  thf('28', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.13/1.37      inference('sup+', [status(thm)], ['26', '27'])).
% 1.13/1.37  thf('29', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 1.13/1.37      inference('demod', [status(thm)], ['23', '28'])).
% 1.13/1.37  thf(t49_xboole_1, axiom,
% 1.13/1.37    (![A:$i,B:$i,C:$i]:
% 1.13/1.37     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.13/1.37       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.13/1.37  thf('30', plain,
% 1.13/1.37      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.13/1.37         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 1.13/1.37           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 1.13/1.37      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.13/1.37  thf('31', plain,
% 1.13/1.37      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 1.13/1.37      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.13/1.37  thf('32', plain,
% 1.13/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.37         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 1.13/1.37      inference('sup+', [status(thm)], ['30', '31'])).
% 1.13/1.37  thf('33', plain,
% 1.13/1.37      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C)),
% 1.13/1.37      inference('sup+', [status(thm)], ['29', '32'])).
% 1.13/1.37  thf('34', plain,
% 1.13/1.37      (![X2 : $i, X3 : $i]:
% 1.13/1.37         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.13/1.37      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.13/1.37  thf('35', plain,
% 1.13/1.37      (![X0 : $i]:
% 1.13/1.37         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C) = (k1_xboole_0))),
% 1.13/1.37      inference('sup-', [status(thm)], ['33', '34'])).
% 1.13/1.37  thf('36', plain,
% 1.13/1.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.13/1.37  thf('37', plain,
% 1.13/1.37      (![X0 : $i]:
% 1.13/1.37         ((k3_xboole_0 @ sk_C @ (k3_xboole_0 @ X0 @ sk_A)) = (k1_xboole_0))),
% 1.13/1.37      inference('demod', [status(thm)], ['35', '36'])).
% 1.13/1.37  thf('38', plain,
% 1.13/1.37      (![X0 : $i, X1 : $i]:
% 1.13/1.37         ((k4_xboole_0 @ X0 @ X1)
% 1.13/1.37           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.13/1.37      inference('sup+', [status(thm)], ['20', '21'])).
% 1.13/1.37  thf('39', plain,
% 1.13/1.37      (![X0 : $i]:
% 1.13/1.37         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C)
% 1.13/1.37           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ k1_xboole_0))),
% 1.13/1.37      inference('sup+', [status(thm)], ['37', '38'])).
% 1.13/1.37  thf('40', plain,
% 1.13/1.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.13/1.37  thf('41', plain,
% 1.13/1.37      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.13/1.37         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 1.13/1.37           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 1.13/1.37      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.13/1.37  thf('42', plain,
% 1.13/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.37         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 1.13/1.37           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 1.13/1.37      inference('sup+', [status(thm)], ['40', '41'])).
% 1.13/1.37  thf('43', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.13/1.37      inference('sup+', [status(thm)], ['26', '27'])).
% 1.13/1.37  thf('44', plain,
% 1.13/1.37      (![X0 : $i]:
% 1.13/1.37         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 1.20/1.37           = (k3_xboole_0 @ X0 @ sk_A))),
% 1.20/1.37      inference('demod', [status(thm)], ['39', '42', '43'])).
% 1.20/1.37  thf('45', plain,
% 1.20/1.37      (![X8 : $i, X9 : $i]:
% 1.20/1.37         ((k4_xboole_0 @ X8 @ X9)
% 1.20/1.37           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.20/1.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.20/1.37  thf('46', plain,
% 1.20/1.37      (![X0 : $i]:
% 1.20/1.37         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 1.20/1.37           = (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_A)))),
% 1.20/1.37      inference('sup+', [status(thm)], ['44', '45'])).
% 1.20/1.37  thf('47', plain,
% 1.20/1.37      (![X0 : $i, X1 : $i]:
% 1.20/1.37         ((k4_xboole_0 @ X0 @ X1)
% 1.20/1.37           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.20/1.37      inference('sup+', [status(thm)], ['20', '21'])).
% 1.20/1.37  thf('48', plain,
% 1.20/1.37      (![X0 : $i]:
% 1.20/1.37         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 1.20/1.37           = (k4_xboole_0 @ sk_A @ X0))),
% 1.20/1.37      inference('demod', [status(thm)], ['46', '47'])).
% 1.20/1.37  thf('49', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 1.20/1.37      inference('demod', [status(thm)], ['14', '48'])).
% 1.20/1.37  thf('50', plain,
% 1.20/1.37      (![X5 : $i, X6 : $i]:
% 1.20/1.37         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 1.20/1.37      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.20/1.37  thf('51', plain,
% 1.20/1.37      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 1.20/1.37      inference('sup-', [status(thm)], ['49', '50'])).
% 1.20/1.37  thf('52', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.20/1.37      inference('simplify', [status(thm)], ['51'])).
% 1.20/1.37  thf('53', plain, ($false), inference('demod', [status(thm)], ['11', '52'])).
% 1.20/1.37  
% 1.20/1.37  % SZS output end Refutation
% 1.20/1.37  
% 1.20/1.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
