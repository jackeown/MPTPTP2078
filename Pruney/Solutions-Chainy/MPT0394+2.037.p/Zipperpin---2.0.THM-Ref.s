%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WaxQ53glxJ

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:49 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 176 expanded)
%              Number of leaves         :   24 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  463 (1345 expanded)
%              Number of equality atoms :   61 ( 176 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X9 @ X10 @ X11 ) @ ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X16 @ X16 @ X17 @ X18 )
      = ( k1_enumset1 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X25: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X23 @ X24 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X23 ) @ ( k1_setfam_1 @ X24 ) ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X1 ) @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ ( k1_tarski @ X1 ) ) @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X25: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X22 ) )
      | ( X21 != X22 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('19',plain,(
    ! [X22: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X22 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k4_xboole_0 @ X6 @ X8 )
       != X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != X1 )
      | ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','35'])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','36'])).

thf('38',plain,(
    ! [X22: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X22 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('39',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','36'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','35'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['39','40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WaxQ53glxJ
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:45:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 380 iterations in 0.170s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.62  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.39/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.39/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.62  thf(t69_enumset1, axiom,
% 0.39/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.62  thf('0', plain, (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.62  thf(t70_enumset1, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      (![X14 : $i, X15 : $i]:
% 0.39/0.62         ((k1_enumset1 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.39/0.62  thf(t46_enumset1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.39/0.62       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.62         ((k2_enumset1 @ X9 @ X10 @ X11 @ X12)
% 0.39/0.62           = (k2_xboole_0 @ (k1_enumset1 @ X9 @ X10 @ X11) @ (k1_tarski @ X12)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.39/0.62  thf('3', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.39/0.62           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['1', '2'])).
% 0.39/0.62  thf(t71_enumset1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.39/0.62  thf('4', plain,
% 0.39/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.62         ((k2_enumset1 @ X16 @ X16 @ X17 @ X18)
% 0.39/0.62           = (k1_enumset1 @ X16 @ X17 @ X18))),
% 0.39/0.62      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      (![X14 : $i, X15 : $i]:
% 0.39/0.62         ((k1_enumset1 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['4', '5'])).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0))
% 0.39/0.62           = (k2_tarski @ X1 @ X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['3', '6'])).
% 0.39/0.62  thf('8', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.39/0.62           = (k2_tarski @ X0 @ X1))),
% 0.39/0.62      inference('sup+', [status(thm)], ['0', '7'])).
% 0.39/0.62  thf(t11_setfam_1, axiom,
% 0.39/0.62    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.39/0.62  thf('9', plain, (![X25 : $i]: ((k1_setfam_1 @ (k1_tarski @ X25)) = (X25))),
% 0.39/0.62      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.39/0.62  thf(t10_setfam_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.39/0.62          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.39/0.62            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.39/0.62  thf('10', plain,
% 0.39/0.62      (![X23 : $i, X24 : $i]:
% 0.39/0.62         (((X23) = (k1_xboole_0))
% 0.39/0.62          | ((k1_setfam_1 @ (k2_xboole_0 @ X23 @ X24))
% 0.39/0.62              = (k3_xboole_0 @ (k1_setfam_1 @ X23) @ (k1_setfam_1 @ X24)))
% 0.39/0.62          | ((X24) = (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((k1_setfam_1 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.39/0.62            = (k3_xboole_0 @ (k1_setfam_1 @ X1) @ X0))
% 0.39/0.62          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.39/0.62          | ((X1) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.62  thf('12', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.39/0.62            = (k3_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X1)) @ X0))
% 0.39/0.62          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.39/0.62          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['8', '11'])).
% 0.39/0.62  thf('13', plain, (![X25 : $i]: ((k1_setfam_1 @ (k1_tarski @ X25)) = (X25))),
% 0.39/0.62      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.39/0.62  thf('14', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.39/0.62          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.39/0.62          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.62  thf(t12_setfam_1, conjecture,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i,B:$i]:
% 0.39/0.62        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.39/0.62         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('16', plain,
% 0.39/0.62      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.39/0.62        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.62  thf('17', plain,
% 0.39/0.62      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['16'])).
% 0.39/0.62  thf(t16_zfmisc_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.39/0.62          ( ( A ) = ( B ) ) ) ))).
% 0.39/0.62  thf('18', plain,
% 0.39/0.62      (![X21 : $i, X22 : $i]:
% 0.39/0.62         (~ (r1_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X22))
% 0.39/0.62          | ((X21) != (X22)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.39/0.62  thf('19', plain,
% 0.39/0.62      (![X22 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X22))),
% 0.39/0.62      inference('simplify', [status(thm)], ['18'])).
% 0.39/0.62  thf('20', plain,
% 0.39/0.62      ((~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.39/0.62        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['17', '19'])).
% 0.39/0.62  thf(idempotence_k3_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.39/0.62  thf('21', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.39/0.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.39/0.62  thf(t48_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.62  thf('22', plain,
% 0.39/0.62      (![X4 : $i, X5 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.39/0.62           = (k3_xboole_0 @ X4 @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.62  thf(t83_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.62  thf('23', plain,
% 0.39/0.62      (![X6 : $i, X8 : $i]:
% 0.39/0.62         ((r1_xboole_0 @ X6 @ X8) | ((k4_xboole_0 @ X6 @ X8) != (X6)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.39/0.62  thf('24', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X1 @ X0) != (X1))
% 0.39/0.62          | (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.62  thf('25', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((X0) != (X0)) | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['21', '24'])).
% 0.39/0.62  thf('26', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['25'])).
% 0.39/0.62  thf('27', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['25'])).
% 0.39/0.62  thf(d7_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.39/0.62       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.62  thf('28', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.62  thf('29', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.62  thf('30', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.39/0.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.39/0.62  thf('31', plain,
% 0.39/0.62      (![X4 : $i, X5 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.39/0.62           = (k3_xboole_0 @ X4 @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.62  thf('32', plain,
% 0.39/0.62      (![X4 : $i, X5 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.39/0.62           = (k3_xboole_0 @ X4 @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.62  thf('33', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.62           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.39/0.62  thf('34', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X0 @ X0)
% 0.39/0.62           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['30', '33'])).
% 0.39/0.62  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['29', '34'])).
% 0.39/0.62  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.39/0.62      inference('demod', [status(thm)], ['26', '35'])).
% 0.39/0.62  thf('37', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.39/0.62      inference('demod', [status(thm)], ['20', '36'])).
% 0.39/0.62  thf('38', plain,
% 0.39/0.62      (![X22 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X22))),
% 0.39/0.62      inference('simplify', [status(thm)], ['18'])).
% 0.39/0.62  thf('39', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.39/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.39/0.62  thf('40', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.39/0.62      inference('demod', [status(thm)], ['20', '36'])).
% 0.39/0.62  thf('41', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.39/0.62      inference('demod', [status(thm)], ['26', '35'])).
% 0.39/0.62  thf('42', plain, ($false),
% 0.39/0.62      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
