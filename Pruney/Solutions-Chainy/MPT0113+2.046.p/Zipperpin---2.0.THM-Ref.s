%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.usiAGUom3t

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:34 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 123 expanded)
%              Number of leaves         :   21 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  508 ( 850 expanded)
%              Number of equality atoms :   47 (  70 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('14',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['13','22'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('24',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['23','32'])).

thf('34',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['12','33'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('36',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','40'])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['50','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('57',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['41','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.usiAGUom3t
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.78/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.78/0.96  % Solved by: fo/fo7.sh
% 0.78/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.96  % done 689 iterations in 0.503s
% 0.78/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.78/0.96  % SZS output start Refutation
% 0.78/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.78/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.78/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.78/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.78/0.96  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.78/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.78/0.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.78/0.96  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.78/0.96  thf(t106_xboole_1, conjecture,
% 0.78/0.96    (![A:$i,B:$i,C:$i]:
% 0.78/0.96     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.78/0.96       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.78/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.78/0.96    (~( ![A:$i,B:$i,C:$i]:
% 0.78/0.96        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.78/0.96          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.78/0.96    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.78/0.96  thf('0', plain,
% 0.78/0.96      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('1', plain,
% 0.78/0.96      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.78/0.96      inference('split', [status(esa)], ['0'])).
% 0.78/0.96  thf(t48_xboole_1, axiom,
% 0.78/0.96    (![A:$i,B:$i]:
% 0.78/0.96     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.78/0.96  thf('2', plain,
% 0.78/0.96      (![X17 : $i, X18 : $i]:
% 0.78/0.96         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.78/0.96           = (k3_xboole_0 @ X17 @ X18))),
% 0.78/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/0.96  thf(t36_xboole_1, axiom,
% 0.78/0.96    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.78/0.96  thf('3', plain,
% 0.78/0.96      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.78/0.96      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.78/0.96  thf('4', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.78/0.96      inference('sup+', [status(thm)], ['2', '3'])).
% 0.78/0.96  thf(l32_xboole_1, axiom,
% 0.78/0.96    (![A:$i,B:$i]:
% 0.78/0.96     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.78/0.96  thf('5', plain,
% 0.78/0.96      (![X3 : $i, X5 : $i]:
% 0.78/0.96         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.78/0.96      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.78/0.96  thf('6', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i]:
% 0.78/0.96         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.78/0.96      inference('sup-', [status(thm)], ['4', '5'])).
% 0.78/0.96  thf(t49_xboole_1, axiom,
% 0.78/0.96    (![A:$i,B:$i,C:$i]:
% 0.78/0.96     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.78/0.96       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.78/0.96  thf('7', plain,
% 0.78/0.96      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.78/0.96         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.78/0.96           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 0.78/0.96      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.78/0.96  thf('8', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i]:
% 0.78/0.96         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.78/0.96      inference('demod', [status(thm)], ['6', '7'])).
% 0.78/0.96  thf(t100_xboole_1, axiom,
% 0.78/0.96    (![A:$i,B:$i]:
% 0.78/0.96     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.78/0.96  thf('9', plain,
% 0.78/0.96      (![X6 : $i, X7 : $i]:
% 0.78/0.96         ((k4_xboole_0 @ X6 @ X7)
% 0.78/0.96           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.78/0.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/0.96  thf('10', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i]:
% 0.78/0.96         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.78/0.96           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.78/0.96      inference('sup+', [status(thm)], ['8', '9'])).
% 0.78/0.96  thf(t5_boole, axiom,
% 0.78/0.96    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.78/0.96  thf('11', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.78/0.96      inference('cnf', [status(esa)], [t5_boole])).
% 0.78/0.96  thf('12', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i]:
% 0.78/0.96         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.78/0.96      inference('demod', [status(thm)], ['10', '11'])).
% 0.78/0.96  thf('13', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i]:
% 0.78/0.96         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.78/0.96      inference('demod', [status(thm)], ['6', '7'])).
% 0.78/0.96  thf('14', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf(t28_xboole_1, axiom,
% 0.78/0.96    (![A:$i,B:$i]:
% 0.78/0.96     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.78/0.96  thf('15', plain,
% 0.78/0.96      (![X11 : $i, X12 : $i]:
% 0.78/0.96         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.78/0.96      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.78/0.96  thf('16', plain,
% 0.78/0.96      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['14', '15'])).
% 0.78/0.96  thf(t16_xboole_1, axiom,
% 0.78/0.96    (![A:$i,B:$i,C:$i]:
% 0.78/0.96     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.78/0.96       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.78/0.96  thf('17', plain,
% 0.78/0.96      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.78/0.96         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 0.78/0.96           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.78/0.96      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.78/0.96  thf('18', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((k3_xboole_0 @ sk_A @ X0)
% 0.78/0.96           = (k3_xboole_0 @ sk_A @ 
% 0.78/0.96              (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 0.78/0.96      inference('sup+', [status(thm)], ['16', '17'])).
% 0.78/0.96  thf('19', plain,
% 0.78/0.96      (![X6 : $i, X7 : $i]:
% 0.78/0.96         ((k4_xboole_0 @ X6 @ X7)
% 0.78/0.96           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.78/0.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/0.96  thf('20', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((k4_xboole_0 @ sk_A @ 
% 0.78/0.96           (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))
% 0.78/0.96           = (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.78/0.96      inference('sup+', [status(thm)], ['18', '19'])).
% 0.78/0.96  thf('21', plain,
% 0.78/0.96      (![X6 : $i, X7 : $i]:
% 0.78/0.96         ((k4_xboole_0 @ X6 @ X7)
% 0.78/0.96           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.78/0.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/0.96  thf('22', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((k4_xboole_0 @ sk_A @ 
% 0.78/0.96           (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))
% 0.78/0.96           = (k4_xboole_0 @ sk_A @ X0))),
% 0.78/0.96      inference('demod', [status(thm)], ['20', '21'])).
% 0.78/0.96  thf('23', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.78/0.96           = (k4_xboole_0 @ sk_A @ 
% 0.78/0.96              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 0.78/0.96      inference('sup+', [status(thm)], ['13', '22'])).
% 0.78/0.96  thf(idempotence_k3_xboole_0, axiom,
% 0.78/0.96    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.78/0.96  thf('24', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.78/0.96      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.78/0.96  thf('25', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.78/0.96      inference('sup+', [status(thm)], ['2', '3'])).
% 0.78/0.96  thf('26', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.78/0.96      inference('sup+', [status(thm)], ['24', '25'])).
% 0.78/0.96  thf('27', plain,
% 0.78/0.96      (![X3 : $i, X5 : $i]:
% 0.78/0.96         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.78/0.96      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.78/0.96  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.78/0.96      inference('sup-', [status(thm)], ['26', '27'])).
% 0.78/0.96  thf('29', plain,
% 0.78/0.96      (![X17 : $i, X18 : $i]:
% 0.78/0.96         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.78/0.96           = (k3_xboole_0 @ X17 @ X18))),
% 0.78/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/0.96  thf('30', plain,
% 0.78/0.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.78/0.96      inference('sup+', [status(thm)], ['28', '29'])).
% 0.78/0.96  thf('31', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.78/0.96      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.78/0.96  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.78/0.96      inference('demod', [status(thm)], ['30', '31'])).
% 0.78/0.96  thf('33', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((sk_A)
% 0.78/0.96           = (k4_xboole_0 @ sk_A @ 
% 0.78/0.96              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 0.78/0.96      inference('demod', [status(thm)], ['23', '32'])).
% 0.78/0.96  thf('34', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.78/0.96      inference('sup+', [status(thm)], ['12', '33'])).
% 0.78/0.96  thf(t79_xboole_1, axiom,
% 0.78/0.96    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.78/0.96  thf('35', plain,
% 0.78/0.96      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 0.78/0.96      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.78/0.96  thf('36', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.78/0.96      inference('sup+', [status(thm)], ['34', '35'])).
% 0.78/0.96  thf('37', plain,
% 0.78/0.96      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.78/0.96      inference('split', [status(esa)], ['0'])).
% 0.78/0.96  thf('38', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.78/0.96      inference('sup-', [status(thm)], ['36', '37'])).
% 0.78/0.96  thf('39', plain,
% 0.78/0.96      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.78/0.96      inference('split', [status(esa)], ['0'])).
% 0.78/0.96  thf('40', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.78/0.96      inference('sat_resolution*', [status(thm)], ['38', '39'])).
% 0.78/0.96  thf('41', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.78/0.96      inference('simpl_trail', [status(thm)], ['1', '40'])).
% 0.78/0.96  thf('42', plain,
% 0.78/0.96      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['14', '15'])).
% 0.78/0.96  thf('43', plain,
% 0.78/0.96      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.78/0.96         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.78/0.96           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 0.78/0.96      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.78/0.96  thf('44', plain,
% 0.78/0.96      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.78/0.96      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.78/0.96  thf('45', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.96         (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.78/0.96          (k3_xboole_0 @ X2 @ X1))),
% 0.78/0.96      inference('sup+', [status(thm)], ['43', '44'])).
% 0.78/0.96  thf('46', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.78/0.96      inference('sup+', [status(thm)], ['42', '45'])).
% 0.78/0.96  thf(commutativity_k3_xboole_0, axiom,
% 0.78/0.96    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.78/0.96  thf('47', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.78/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.78/0.96  thf('48', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.78/0.96      inference('demod', [status(thm)], ['46', '47'])).
% 0.78/0.96  thf('49', plain,
% 0.78/0.96      (![X11 : $i, X12 : $i]:
% 0.78/0.96         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.78/0.96      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.78/0.96  thf('50', plain,
% 0.78/0.96      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['48', '49'])).
% 0.78/0.96  thf('51', plain,
% 0.78/0.96      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.78/0.96         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 0.78/0.96           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.78/0.96      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.78/0.96  thf('52', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.78/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.78/0.96  thf('53', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.96         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 0.78/0.96           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.78/0.96      inference('sup+', [status(thm)], ['51', '52'])).
% 0.78/0.96  thf('54', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.78/0.96      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.78/0.96  thf('55', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.78/0.96      inference('demod', [status(thm)], ['50', '53', '54'])).
% 0.78/0.96  thf('56', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.78/0.96      inference('sup+', [status(thm)], ['2', '3'])).
% 0.78/0.96  thf('57', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.78/0.96      inference('sup+', [status(thm)], ['55', '56'])).
% 0.78/0.96  thf('58', plain, ($false), inference('demod', [status(thm)], ['41', '57'])).
% 0.78/0.96  
% 0.78/0.96  % SZS output end Refutation
% 0.78/0.96  
% 0.78/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
