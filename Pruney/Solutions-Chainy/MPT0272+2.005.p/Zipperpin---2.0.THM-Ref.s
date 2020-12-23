%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1fjT0bzEko

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:26 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 141 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :   18
%              Number of atoms          :  480 (1128 expanded)
%              Number of equality atoms :   45 ( 102 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( r2_hidden @ X46 @ X47 )
      | ~ ( r1_tarski @ ( k2_tarski @ X46 @ X48 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k5_xboole_0 @ X6 @ X8 ) )
      | ( r2_hidden @ X5 @ X8 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t53_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X50 @ X51 )
      | ~ ( r2_hidden @ X52 @ X51 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X50 @ X52 ) @ X51 )
        = ( k2_tarski @ X50 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t53_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X1 @ X2 ) @ ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
        = ( k2_tarski @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
        = ( k2_tarski @ X1 @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X14 @ X16 ) @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t69_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t69_zfmisc_1])).

thf('25',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['26'])).

thf('29',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X50 @ X51 )
      | ~ ( r2_hidden @ X52 @ X51 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X50 @ X52 ) @ X51 )
        = ( k2_tarski @ X50 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t53_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_B )
        = ( k2_tarski @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_A ) )
    = ( k2_tarski @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('38',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('39',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('40',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1fjT0bzEko
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.69/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.91  % Solved by: fo/fo7.sh
% 0.69/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.91  % done 994 iterations in 0.438s
% 0.69/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.91  % SZS output start Refutation
% 0.69/0.91  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.69/0.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.69/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.91  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.69/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.91  thf(t69_enumset1, axiom,
% 0.69/0.91    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.69/0.91  thf('0', plain, (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.69/0.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.69/0.91  thf(d10_xboole_0, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.69/0.91  thf('1', plain,
% 0.69/0.91      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 0.69/0.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.91  thf('2', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.69/0.91      inference('simplify', [status(thm)], ['1'])).
% 0.69/0.91  thf(t38_zfmisc_1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.69/0.91       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.69/0.91  thf('3', plain,
% 0.69/0.91      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.69/0.91         ((r2_hidden @ X46 @ X47)
% 0.69/0.91          | ~ (r1_tarski @ (k2_tarski @ X46 @ X48) @ X47))),
% 0.69/0.91      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.69/0.91  thf('4', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['2', '3'])).
% 0.69/0.91  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.69/0.91      inference('sup+', [status(thm)], ['0', '4'])).
% 0.69/0.91  thf(t1_xboole_0, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.69/0.91       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.69/0.91  thf('6', plain,
% 0.69/0.91      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.69/0.91         ((r2_hidden @ X5 @ (k5_xboole_0 @ X6 @ X8))
% 0.69/0.91          | (r2_hidden @ X5 @ X8)
% 0.69/0.91          | ~ (r2_hidden @ X5 @ X6))),
% 0.69/0.91      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.69/0.91  thf('7', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         ((r2_hidden @ X0 @ X1)
% 0.69/0.91          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['5', '6'])).
% 0.69/0.91  thf('8', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         ((r2_hidden @ X0 @ X1)
% 0.69/0.91          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['5', '6'])).
% 0.69/0.91  thf(t53_zfmisc_1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.69/0.91       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 0.69/0.91  thf('9', plain,
% 0.69/0.91      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.69/0.91         (~ (r2_hidden @ X50 @ X51)
% 0.69/0.91          | ~ (r2_hidden @ X52 @ X51)
% 0.69/0.91          | ((k3_xboole_0 @ (k2_tarski @ X50 @ X52) @ X51)
% 0.69/0.91              = (k2_tarski @ X50 @ X52)))),
% 0.69/0.91      inference('cnf', [status(esa)], [t53_zfmisc_1])).
% 0.69/0.91  thf('10', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.91         ((r2_hidden @ X1 @ X0)
% 0.69/0.91          | ((k3_xboole_0 @ (k2_tarski @ X1 @ X2) @ 
% 0.69/0.91              (k5_xboole_0 @ (k1_tarski @ X1) @ X0)) = (k2_tarski @ X1 @ X2))
% 0.69/0.91          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['8', '9'])).
% 0.69/0.91  thf('11', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         ((r2_hidden @ X1 @ X0)
% 0.69/0.91          | ((k3_xboole_0 @ (k2_tarski @ X1 @ X1) @ 
% 0.69/0.91              (k5_xboole_0 @ (k1_tarski @ X1) @ X0)) = (k2_tarski @ X1 @ X1))
% 0.69/0.91          | (r2_hidden @ X1 @ X0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['7', '10'])).
% 0.69/0.91  thf('12', plain,
% 0.69/0.91      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.69/0.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.69/0.91  thf(idempotence_k3_xboole_0, axiom,
% 0.69/0.91    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.69/0.91  thf('13', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.69/0.91      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.69/0.91  thf(t112_xboole_1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.69/0.91       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.69/0.91  thf('14', plain,
% 0.69/0.91      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.69/0.91         ((k5_xboole_0 @ (k3_xboole_0 @ X14 @ X16) @ (k3_xboole_0 @ X15 @ X16))
% 0.69/0.91           = (k3_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16))),
% 0.69/0.91      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.69/0.91  thf('15', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.69/0.91           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0))),
% 0.69/0.91      inference('sup+', [status(thm)], ['13', '14'])).
% 0.69/0.91  thf(commutativity_k3_xboole_0, axiom,
% 0.69/0.91    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.69/0.91  thf('16', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.69/0.91  thf('17', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.69/0.91           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.69/0.91      inference('demod', [status(thm)], ['15', '16'])).
% 0.69/0.91  thf('18', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.69/0.91  thf(t100_xboole_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.69/0.91  thf('19', plain,
% 0.69/0.91      (![X12 : $i, X13 : $i]:
% 0.69/0.91         ((k4_xboole_0 @ X12 @ X13)
% 0.69/0.91           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.69/0.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.69/0.91  thf('20', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         ((k4_xboole_0 @ X0 @ X1)
% 0.69/0.91           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.69/0.91      inference('sup+', [status(thm)], ['18', '19'])).
% 0.69/0.91  thf('21', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         ((k4_xboole_0 @ X1 @ X0)
% 0.69/0.91           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.69/0.91      inference('sup+', [status(thm)], ['17', '20'])).
% 0.69/0.91  thf('22', plain,
% 0.69/0.91      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.69/0.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.69/0.91  thf('23', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         ((r2_hidden @ X1 @ X0)
% 0.69/0.91          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 0.69/0.91          | (r2_hidden @ X1 @ X0))),
% 0.69/0.91      inference('demod', [status(thm)], ['11', '12', '21', '22'])).
% 0.69/0.91  thf('24', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 0.69/0.91          | (r2_hidden @ X1 @ X0))),
% 0.69/0.91      inference('simplify', [status(thm)], ['23'])).
% 0.69/0.91  thf(t69_zfmisc_1, conjecture,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.69/0.91       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 0.69/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.91    (~( ![A:$i,B:$i]:
% 0.69/0.91        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.69/0.91          ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.69/0.91    inference('cnf.neg', [status(esa)], [t69_zfmisc_1])).
% 0.69/0.91  thf('25', plain,
% 0.69/0.91      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('26', plain,
% 0.69/0.91      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.69/0.91      inference('sup-', [status(thm)], ['24', '25'])).
% 0.69/0.91  thf('27', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.69/0.91      inference('simplify', [status(thm)], ['26'])).
% 0.69/0.91  thf('28', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.69/0.91      inference('simplify', [status(thm)], ['26'])).
% 0.69/0.91  thf('29', plain,
% 0.69/0.91      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.69/0.91         (~ (r2_hidden @ X50 @ X51)
% 0.69/0.91          | ~ (r2_hidden @ X52 @ X51)
% 0.69/0.91          | ((k3_xboole_0 @ (k2_tarski @ X50 @ X52) @ X51)
% 0.69/0.91              = (k2_tarski @ X50 @ X52)))),
% 0.69/0.91      inference('cnf', [status(esa)], [t53_zfmisc_1])).
% 0.69/0.91  thf('30', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (((k3_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_B)
% 0.69/0.91            = (k2_tarski @ sk_A @ X0))
% 0.69/0.91          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.69/0.91      inference('sup-', [status(thm)], ['28', '29'])).
% 0.69/0.91  thf('31', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.69/0.91  thf('32', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ X0))
% 0.69/0.91            = (k2_tarski @ sk_A @ X0))
% 0.69/0.91          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.69/0.91      inference('demod', [status(thm)], ['30', '31'])).
% 0.69/0.91  thf('33', plain,
% 0.69/0.91      (((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_A))
% 0.69/0.91         = (k2_tarski @ sk_A @ sk_A))),
% 0.69/0.91      inference('sup-', [status(thm)], ['27', '32'])).
% 0.69/0.91  thf('34', plain,
% 0.69/0.91      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.69/0.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.69/0.91  thf('35', plain,
% 0.69/0.91      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.69/0.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.69/0.91  thf('36', plain,
% 0.69/0.91      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.69/0.91      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.69/0.91  thf('37', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         ((k4_xboole_0 @ X0 @ X1)
% 0.69/0.91           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.69/0.91      inference('sup+', [status(thm)], ['18', '19'])).
% 0.69/0.91  thf('38', plain,
% 0.69/0.91      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.69/0.91         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.69/0.91      inference('sup+', [status(thm)], ['36', '37'])).
% 0.69/0.91  thf(t92_xboole_1, axiom,
% 0.69/0.91    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.69/0.91  thf('39', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.69/0.91      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.69/0.91  thf('40', plain,
% 0.69/0.91      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.69/0.91      inference('demod', [status(thm)], ['38', '39'])).
% 0.69/0.91  thf('41', plain,
% 0.69/0.91      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('42', plain, ($false),
% 0.69/0.91      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.69/0.91  
% 0.69/0.91  % SZS output end Refutation
% 0.69/0.91  
% 0.69/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
