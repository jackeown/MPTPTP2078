%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VXISwIQ72m

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:15 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :   14 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  239 ( 312 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t75_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t75_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('4',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t54_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VXISwIQ72m
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:45:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 24 iterations in 0.026s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(t75_xboole_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.48          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i]:
% 0.19/0.48        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.48             ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t75_xboole_1])).
% 0.19/0.48  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t4_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X1 @ X2)
% 0.19/0.48          | (r2_hidden @ (sk_C @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.48  thf(t16_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.19/0.48       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.48         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 0.19/0.48           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.19/0.48          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.19/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.19/0.48          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.19/0.48          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '5'])).
% 0.19/0.48  thf('7', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '6'])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X1 @ X2)
% 0.19/0.48          | (r2_hidden @ (sk_C @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.48  thf(t54_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.19/0.48       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15))
% 0.19/0.48           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 0.19/0.48              (k4_xboole_0 @ X13 @ X15)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t54_xboole_1])).
% 0.19/0.48  thf(idempotence_k2_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.48  thf('10', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0))
% 0.19/0.48           = (k4_xboole_0 @ X1 @ X0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf(t48_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.19/0.48           = (k3_xboole_0 @ X11 @ X12))),
% 0.19/0.48      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.19/0.48           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.19/0.48           = (k3_xboole_0 @ X11 @ X12))),
% 0.19/0.48      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k3_xboole_0 @ X1 @ X0)
% 0.19/0.48           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.19/0.48          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.19/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.19/0.48          | ~ (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X1 @ X0)
% 0.19/0.48          | ~ (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['8', '17'])).
% 0.19/0.48  thf('19', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.19/0.48      inference('sup-', [status(thm)], ['7', '18'])).
% 0.19/0.48  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
