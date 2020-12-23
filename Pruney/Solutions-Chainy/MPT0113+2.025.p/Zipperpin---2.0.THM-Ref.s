%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LLa6EpbNtE

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:32 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   63 (  89 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  364 ( 589 expanded)
%              Number of equality atoms :   30 (  42 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('2',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t82_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t82_xboole_1])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X17: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X17 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ( r1_xboole_0 @ X20 @ ( k4_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference('sup+',[status(thm)],['4','14'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('17',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','21'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('27',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['22','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LLa6EpbNtE
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 323 iterations in 0.148s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.42/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.60  thf(t106_xboole_1, conjecture,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.42/0.60       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.42/0.60        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.42/0.60          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.42/0.60  thf('0', plain,
% 0.42/0.60      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.42/0.60      inference('split', [status(esa)], ['0'])).
% 0.42/0.60  thf('2', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(t28_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (![X9 : $i, X10 : $i]:
% 0.42/0.60         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.42/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.60  thf(t49_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.42/0.60       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.60         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.42/0.60           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.42/0.60      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.42/0.60  thf(t82_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ))).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      (![X18 : $i, X19 : $i]:
% 0.42/0.60         (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X19 @ X18))),
% 0.42/0.60      inference('cnf', [status(esa)], [t82_xboole_1])).
% 0.42/0.60  thf(t66_xboole_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.42/0.60       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      (![X17 : $i]: (((X17) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X17 @ X17))),
% 0.42/0.60      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.42/0.60  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.60  thf(l32_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.60  thf('9', plain,
% 0.42/0.60      (![X4 : $i, X5 : $i]:
% 0.42/0.60         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ X0 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.60  thf('11', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.42/0.60      inference('simplify', [status(thm)], ['10'])).
% 0.42/0.60  thf(t85_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.42/0.60  thf('12', plain,
% 0.42/0.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.42/0.60         (~ (r1_tarski @ X20 @ X21)
% 0.42/0.60          | (r1_xboole_0 @ X20 @ (k4_xboole_0 @ X22 @ X21)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.42/0.60      inference('sup+', [status(thm)], ['5', '13'])).
% 0.42/0.60  thf('15', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.42/0.60      inference('sup+', [status(thm)], ['4', '14'])).
% 0.42/0.60  thf(symmetry_r1_xboole_0, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      (![X2 : $i, X3 : $i]:
% 0.42/0.60         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.42/0.60      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.42/0.60  thf('17', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.42/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.60  thf('18', plain,
% 0.42/0.60      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.42/0.60      inference('split', [status(esa)], ['0'])).
% 0.42/0.60  thf('19', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.42/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.42/0.60  thf('20', plain,
% 0.42/0.60      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.42/0.60      inference('split', [status(esa)], ['0'])).
% 0.42/0.60  thf('21', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.42/0.60      inference('sat_resolution*', [status(thm)], ['19', '20'])).
% 0.42/0.60  thf('22', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.42/0.60      inference('simpl_trail', [status(thm)], ['1', '21'])).
% 0.42/0.60  thf(t36_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.42/0.60  thf('23', plain,
% 0.42/0.60      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.42/0.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.42/0.60  thf('24', plain,
% 0.42/0.60      (![X4 : $i, X6 : $i]:
% 0.42/0.60         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.42/0.60      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.42/0.60  thf('25', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.42/0.60  thf('26', plain,
% 0.42/0.60      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.60  thf('27', plain,
% 0.42/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.60         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.42/0.60           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.42/0.60      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.42/0.60  thf('28', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((k3_xboole_0 @ sk_A @ 
% 0.42/0.60           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))
% 0.42/0.60           = (k4_xboole_0 @ sk_A @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['26', '27'])).
% 0.42/0.60  thf('29', plain,
% 0.42/0.60      (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.42/0.60      inference('sup+', [status(thm)], ['25', '28'])).
% 0.42/0.60  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.60  thf('31', plain,
% 0.42/0.60      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.42/0.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.42/0.60  thf('32', plain,
% 0.42/0.60      (![X9 : $i, X10 : $i]:
% 0.42/0.60         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.42/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.42/0.60  thf('33', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.42/0.60           = (k4_xboole_0 @ X0 @ X1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.42/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.42/0.60  thf('34', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.42/0.60  thf('35', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.42/0.60           = (k4_xboole_0 @ X0 @ X1))),
% 0.42/0.60      inference('demod', [status(thm)], ['33', '34'])).
% 0.42/0.60  thf('36', plain,
% 0.42/0.60      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['30', '35'])).
% 0.42/0.60  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.60  thf('38', plain,
% 0.42/0.60      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.60      inference('demod', [status(thm)], ['36', '37'])).
% 0.42/0.60  thf('39', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.42/0.60      inference('demod', [status(thm)], ['29', '38'])).
% 0.42/0.60  thf('40', plain,
% 0.42/0.60      (![X4 : $i, X5 : $i]:
% 0.42/0.60         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.42/0.60  thf('41', plain,
% 0.42/0.60      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.42/0.60  thf('42', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.42/0.60      inference('simplify', [status(thm)], ['41'])).
% 0.42/0.60  thf('43', plain, ($false), inference('demod', [status(thm)], ['22', '42'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
