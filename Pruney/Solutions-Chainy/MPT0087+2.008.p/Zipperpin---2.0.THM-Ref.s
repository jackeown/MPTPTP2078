%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kJbQMlfNAs

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  71 expanded)
%              Number of leaves         :   18 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  362 ( 532 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t80_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t80_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','16'])).

thf('18',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['17','28'])).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kJbQMlfNAs
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:24:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 117 iterations in 0.053s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(t80_xboole_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.51        ( ( r1_xboole_0 @ A @ B ) =>
% 0.21/0.51          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t80_xboole_1])).
% 0.21/0.51  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t51_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.21/0.51       ( A ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 0.21/0.51           = (X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.21/0.51  thf(idempotence_k2_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.51  thf('2', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.51  thf(t46_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.51  thf('4', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf(t41_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.51       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.21/0.51           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k1_xboole_0)
% 0.21/0.51           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf(t39_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.21/0.51           = (k2_xboole_0 @ X11 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 0.21/0.51           = (X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 0.21/0.51           k1_xboole_0) = (X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.21/0.51           = (k2_xboole_0 @ X11 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.51  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.21/0.51           = (k4_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['1', '16'])).
% 0.21/0.51  thf('18', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t3_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.51            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.51  thf(d4_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.51       ( ![D:$i]:
% 0.21/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.51           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.51          | (r2_hidden @ X4 @ X2)
% 0.21/0.51          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.51         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.21/0.51          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['19', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X9 @ X7)
% 0.21/0.51          | ~ (r2_hidden @ X9 @ X10)
% 0.21/0.51          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.51          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.51          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.21/0.51          | ~ (r1_xboole_0 @ X2 @ X0)
% 0.21/0.51          | (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r1_xboole_0 @ X2 @ X0)
% 0.21/0.51          | (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.21/0.51      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['18', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.21/0.51      inference('sup+', [status(thm)], ['17', '28'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.51          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.51          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.51          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.21/0.51          | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['29', '33'])).
% 0.21/0.51  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
