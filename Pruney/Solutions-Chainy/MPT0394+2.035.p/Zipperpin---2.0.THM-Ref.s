%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oyT3tqCzc8

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:49 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 110 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  275 ( 907 expanded)
%              Number of equality atoms :   44 ( 149 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('1',plain,(
    ! [X22: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X20 @ X21 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X20 ) @ ( k1_setfam_1 @ X21 ) ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X22: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X19 ) )
      | ( X18 != X19 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('12',plain,(
    ! [X19: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X19 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','18'])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X19: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X19 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('22',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['19'])).

thf('24',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['17'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['22','23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oyT3tqCzc8
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:35:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 383 iterations in 0.137s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.60  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.42/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.42/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(t41_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( k2_tarski @ A @ B ) =
% 0.42/0.60       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.42/0.60  thf('0', plain,
% 0.42/0.60      (![X4 : $i, X5 : $i]:
% 0.42/0.60         ((k2_tarski @ X4 @ X5)
% 0.42/0.60           = (k2_xboole_0 @ (k1_tarski @ X4) @ (k1_tarski @ X5)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.42/0.60  thf(t11_setfam_1, axiom,
% 0.42/0.60    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.42/0.60  thf('1', plain, (![X22 : $i]: ((k1_setfam_1 @ (k1_tarski @ X22)) = (X22))),
% 0.42/0.60      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.42/0.60  thf(t10_setfam_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.42/0.60          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.42/0.60            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (![X20 : $i, X21 : $i]:
% 0.42/0.60         (((X20) = (k1_xboole_0))
% 0.42/0.60          | ((k1_setfam_1 @ (k2_xboole_0 @ X20 @ X21))
% 0.42/0.60              = (k3_xboole_0 @ (k1_setfam_1 @ X20) @ (k1_setfam_1 @ X21)))
% 0.42/0.60          | ((X21) = (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.42/0.60            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.42/0.60          | ((X1) = (k1_xboole_0))
% 0.42/0.60          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.42/0.60      inference('sup+', [status(thm)], ['1', '2'])).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.42/0.60            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.42/0.60          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.42/0.60          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.42/0.60      inference('sup+', [status(thm)], ['0', '3'])).
% 0.42/0.60  thf('5', plain, (![X22 : $i]: ((k1_setfam_1 @ (k1_tarski @ X22)) = (X22))),
% 0.42/0.60      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.42/0.60          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.42/0.60          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.42/0.60      inference('demod', [status(thm)], ['4', '5'])).
% 0.42/0.60  thf(t12_setfam_1, conjecture,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i,B:$i]:
% 0.42/0.60        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.42/0.60         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.42/0.60        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.42/0.60        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.60  thf('9', plain,
% 0.42/0.60      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.42/0.60        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['8'])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.42/0.60        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['8'])).
% 0.42/0.60  thf(t16_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.42/0.60          ( ( A ) = ( B ) ) ) ))).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X18 : $i, X19 : $i]:
% 0.42/0.60         (~ (r1_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X19))
% 0.42/0.60          | ((X18) != (X19)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.42/0.60  thf('12', plain,
% 0.42/0.60      (![X19 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X19))),
% 0.42/0.60      inference('simplify', [status(thm)], ['11'])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      ((~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.42/0.60        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['10', '12'])).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      ((~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.42/0.60        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.42/0.60        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['9', '13'])).
% 0.42/0.60  thf(idempotence_k3_xboole_0, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.42/0.60  thf('15', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.42/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.42/0.60  thf(d7_xboole_0, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.42/0.60       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      (![X0 : $i, X2 : $i]:
% 0.42/0.60         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.60  thf('18', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.42/0.60      inference('simplify', [status(thm)], ['17'])).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.42/0.60        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.42/0.60      inference('demod', [status(thm)], ['14', '18'])).
% 0.42/0.60  thf('20', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['19'])).
% 0.42/0.60  thf('21', plain,
% 0.42/0.60      (![X19 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X19))),
% 0.42/0.60      inference('simplify', [status(thm)], ['11'])).
% 0.42/0.60  thf('22', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.42/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.60  thf('23', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['19'])).
% 0.42/0.60  thf('24', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.42/0.60      inference('simplify', [status(thm)], ['17'])).
% 0.42/0.60  thf('25', plain, ($false),
% 0.42/0.60      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
