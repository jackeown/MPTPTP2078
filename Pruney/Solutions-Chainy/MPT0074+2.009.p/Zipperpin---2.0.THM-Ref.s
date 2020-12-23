%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ms83D7aozA

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:41 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   52 (  61 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  319 ( 415 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t67_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ B @ C ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t67_xboole_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_tarski @ ( k3_xboole_0 @ X17 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t27_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('6',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t24_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X11 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ X0 ) @ X1 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('25',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','25'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('28',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ms83D7aozA
% 0.15/0.37  % Computer   : n004.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 20:15:24 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.56  % Solved by: fo/fo7.sh
% 0.24/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.56  % done 97 iterations in 0.074s
% 0.24/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.56  % SZS output start Refutation
% 0.24/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.24/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.24/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.56  thf(t67_xboole_1, conjecture,
% 0.24/0.56    (![A:$i,B:$i,C:$i]:
% 0.24/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.24/0.56         ( r1_xboole_0 @ B @ C ) ) =>
% 0.24/0.56       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.56        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.24/0.56            ( r1_xboole_0 @ B @ C ) ) =>
% 0.24/0.56          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.24/0.56    inference('cnf.neg', [status(esa)], [t67_xboole_1])).
% 0.24/0.56  thf('0', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf(t27_xboole_1, axiom,
% 0.24/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.24/0.56       ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ))).
% 0.24/0.56  thf('2', plain,
% 0.24/0.56      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.24/0.56         (~ (r1_tarski @ X17 @ X18)
% 0.24/0.56          | ~ (r1_tarski @ X19 @ X20)
% 0.24/0.56          | (r1_tarski @ (k3_xboole_0 @ X17 @ X19) @ (k3_xboole_0 @ X18 @ X20)))),
% 0.24/0.56      inference('cnf', [status(esa)], [t27_xboole_1])).
% 0.24/0.56  thf('3', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         ((r1_tarski @ (k3_xboole_0 @ sk_A @ X1) @ (k3_xboole_0 @ sk_B @ X0))
% 0.24/0.56          | ~ (r1_tarski @ X1 @ X0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.56  thf('4', plain,
% 0.24/0.56      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.24/0.56      inference('sup-', [status(thm)], ['0', '3'])).
% 0.24/0.56  thf(idempotence_k2_xboole_0, axiom,
% 0.24/0.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.24/0.56  thf('5', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.24/0.56      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.24/0.56  thf('6', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.24/0.56      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.24/0.56  thf(t24_xboole_1, axiom,
% 0.24/0.56    (![A:$i,B:$i,C:$i]:
% 0.24/0.56     ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.24/0.56       ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ))).
% 0.24/0.56  thf('7', plain,
% 0.24/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.24/0.56         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X15 @ X16))
% 0.24/0.56           = (k3_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ 
% 0.24/0.56              (k2_xboole_0 @ X14 @ X16)))),
% 0.24/0.56      inference('cnf', [status(esa)], [t24_xboole_1])).
% 0.24/0.56  thf('8', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.24/0.56           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.24/0.56      inference('sup+', [status(thm)], ['6', '7'])).
% 0.24/0.56  thf('9', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0))
% 0.24/0.56           = (k3_xboole_0 @ X0 @ X0))),
% 0.24/0.56      inference('sup+', [status(thm)], ['5', '8'])).
% 0.24/0.56  thf(t11_xboole_1, axiom,
% 0.24/0.56    (![A:$i,B:$i,C:$i]:
% 0.24/0.56     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.24/0.56  thf('10', plain,
% 0.24/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.24/0.56         ((r1_tarski @ X11 @ X12)
% 0.24/0.56          | ~ (r1_tarski @ (k2_xboole_0 @ X11 @ X13) @ X12))),
% 0.24/0.56      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.24/0.56  thf('11', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ X0) @ X1) | (r1_tarski @ X0 @ X1))),
% 0.24/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.24/0.56  thf('12', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.24/0.56      inference('sup-', [status(thm)], ['4', '11'])).
% 0.24/0.56  thf('13', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf(d5_xboole_0, axiom,
% 0.24/0.56    (![A:$i,B:$i,C:$i]:
% 0.24/0.56     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.24/0.56       ( ![D:$i]:
% 0.24/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.24/0.56           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.24/0.56  thf('14', plain,
% 0.24/0.56      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.24/0.56         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.24/0.56          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.24/0.56          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.24/0.56      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.24/0.56  thf(t3_boole, axiom,
% 0.24/0.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.24/0.56  thf('15', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.24/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.24/0.56  thf('16', plain,
% 0.24/0.56      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.24/0.56         (~ (r2_hidden @ X4 @ X3)
% 0.24/0.56          | ~ (r2_hidden @ X4 @ X2)
% 0.24/0.56          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.24/0.56      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.24/0.56  thf('17', plain,
% 0.24/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.24/0.56         (~ (r2_hidden @ X4 @ X2)
% 0.24/0.56          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.24/0.56      inference('simplify', [status(thm)], ['16'])).
% 0.24/0.56  thf('18', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['15', '17'])).
% 0.24/0.56  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.24/0.56      inference('condensation', [status(thm)], ['18'])).
% 0.24/0.56  thf('20', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.24/0.56          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['14', '19'])).
% 0.24/0.56  thf(t4_xboole_0, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.24/0.56            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.24/0.56  thf('21', plain,
% 0.24/0.56      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.24/0.56         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.24/0.56          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.24/0.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.24/0.56  thf('22', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.56         (((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 0.24/0.56          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.56  thf('23', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ X0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['13', '22'])).
% 0.24/0.56  thf('24', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.24/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.24/0.56  thf('25', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.24/0.56      inference('sup+', [status(thm)], ['23', '24'])).
% 0.24/0.56  thf('26', plain, ((r1_tarski @ sk_A @ k1_xboole_0)),
% 0.24/0.56      inference('demod', [status(thm)], ['12', '25'])).
% 0.24/0.56  thf(t3_xboole_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.56  thf('27', plain,
% 0.24/0.56      (![X22 : $i]:
% 0.24/0.56         (((X22) = (k1_xboole_0)) | ~ (r1_tarski @ X22 @ k1_xboole_0))),
% 0.24/0.56      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.24/0.56  thf('28', plain, (((sk_A) = (k1_xboole_0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.24/0.56  thf('29', plain, (((sk_A) != (k1_xboole_0))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('30', plain, ($false),
% 0.24/0.56      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.24/0.56  
% 0.24/0.56  % SZS output end Refutation
% 0.24/0.56  
% 0.24/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
