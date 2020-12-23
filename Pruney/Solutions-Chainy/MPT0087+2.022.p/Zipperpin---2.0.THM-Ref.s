%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cect2mGKQh

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:34 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   47 (  58 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  337 ( 489 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      | ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('11',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X9 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

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

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['4','20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      | ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_A @ X0 )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','27'])).

thf('29',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X9 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cect2mGKQh
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.97  % Solved by: fo/fo7.sh
% 0.76/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.97  % done 383 iterations in 0.486s
% 0.76/0.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.97  % SZS output start Refutation
% 0.76/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.97  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.76/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.97  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.76/0.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.76/0.97  thf(t80_xboole_1, conjecture,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.76/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.97    (~( ![A:$i,B:$i,C:$i]:
% 0.76/0.97        ( ( r1_xboole_0 @ A @ B ) =>
% 0.76/0.97          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )),
% 0.76/0.97    inference('cnf.neg', [status(esa)], [t80_xboole_1])).
% 0.76/0.97  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(t41_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.76/0.97       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.76/0.97  thf('1', plain,
% 0.76/0.97      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.76/0.97         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.76/0.97           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.76/0.97  thf(t39_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.76/0.97  thf('2', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i]:
% 0.76/0.97         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.76/0.97           = (k2_xboole_0 @ X4 @ X5))),
% 0.76/0.97      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.76/0.97  thf('3', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.76/0.97           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.76/0.97      inference('sup+', [status(thm)], ['1', '2'])).
% 0.76/0.97  thf('4', plain,
% 0.76/0.97      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.76/0.97         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.76/0.97           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.76/0.97  thf(t79_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.76/0.97  thf('5', plain,
% 0.76/0.97      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 0.76/0.97      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.76/0.97  thf('6', plain,
% 0.76/0.97      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 0.76/0.97      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.76/0.97  thf(t70_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.76/0.97            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.76/0.97       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.76/0.97            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.76/0.97  thf('7', plain,
% 0.76/0.97      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.97         ((r1_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 0.76/0.97          | ~ (r1_xboole_0 @ X9 @ X10)
% 0.76/0.97          | ~ (r1_xboole_0 @ X9 @ X11))),
% 0.76/0.97      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.76/0.97  thf('8', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.76/0.97          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/0.97  thf('9', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['5', '8'])).
% 0.76/0.97  thf('10', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i]:
% 0.76/0.97         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.76/0.97           = (k2_xboole_0 @ X4 @ X5))),
% 0.76/0.97      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.76/0.97  thf('11', plain,
% 0.76/0.97      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.76/0.97         ((r1_xboole_0 @ X9 @ X12)
% 0.76/0.97          | ~ (r1_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X12)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.76/0.97  thf('12', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.76/0.97          | (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['10', '11'])).
% 0.76/0.97  thf('13', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['9', '12'])).
% 0.76/0.97  thf(t3_xboole_0, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.76/0.97            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.76/0.97       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.76/0.97            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.76/0.97  thf('14', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/0.97  thf('15', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/0.97  thf('16', plain,
% 0.76/0.97      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X2 @ X0)
% 0.76/0.97          | ~ (r2_hidden @ X2 @ X3)
% 0.76/0.97          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.76/0.97      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/0.97  thf('17', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((r1_xboole_0 @ X1 @ X0)
% 0.76/0.97          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.76/0.97          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.76/0.97      inference('sup-', [status(thm)], ['15', '16'])).
% 0.76/0.97  thf('18', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((r1_xboole_0 @ X1 @ X0)
% 0.76/0.97          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.76/0.97          | (r1_xboole_0 @ X1 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['14', '17'])).
% 0.76/0.97  thf('19', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X1 @ X0))),
% 0.76/0.97      inference('simplify', [status(thm)], ['18'])).
% 0.76/0.97  thf('20', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['13', '19'])).
% 0.76/0.97  thf('21', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (r1_xboole_0 @ X2 @ 
% 0.76/0.97          (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.76/0.97      inference('sup+', [status(thm)], ['4', '20'])).
% 0.76/0.97  thf('22', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i]:
% 0.76/0.97         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.76/0.97           = (k2_xboole_0 @ X4 @ X5))),
% 0.76/0.97      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.76/0.97  thf('23', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.76/0.97      inference('demod', [status(thm)], ['21', '22'])).
% 0.76/0.97  thf('24', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('25', plain,
% 0.76/0.97      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.97         ((r1_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 0.76/0.97          | ~ (r1_xboole_0 @ X9 @ X10)
% 0.76/0.97          | ~ (r1_xboole_0 @ X9 @ X11))),
% 0.76/0.97      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.76/0.97  thf('26', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (r1_xboole_0 @ sk_A @ X0)
% 0.76/0.97          | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['24', '25'])).
% 0.76/0.97  thf('27', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (r1_xboole_0 @ sk_A @ 
% 0.76/0.97          (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['23', '26'])).
% 0.76/0.97  thf('28', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.76/0.97      inference('sup+', [status(thm)], ['3', '27'])).
% 0.76/0.97  thf('29', plain,
% 0.76/0.97      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.76/0.97         ((r1_xboole_0 @ X9 @ X12)
% 0.76/0.97          | ~ (r1_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X12)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.76/0.97  thf('30', plain,
% 0.76/0.97      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['28', '29'])).
% 0.76/0.97  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.76/0.97  
% 0.76/0.97  % SZS output end Refutation
% 0.76/0.97  
% 0.76/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
