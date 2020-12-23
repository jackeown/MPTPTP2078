%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QoaQeefY8M

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  56 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :   15
%              Number of atoms          :  318 ( 454 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t7_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( ( A = k1_xboole_0 )
          | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X15 @ X14 ) @ X14 )
      | ( r1_tarski @ X15 @ ( k1_setfam_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ! [D: $i] :
            ( ( ( r1_tarski @ D @ B )
              & ( r1_tarski @ D @ C ) )
           => ( r1_tarski @ D @ A ) ) )
     => ( A
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( r1_tarski @ ( sk_D_1 @ X11 @ X10 @ X9 ) @ X11 )
      | ( X9
        = ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k3_xboole_0 @ sk_B @ X0 ) )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r1_tarski @ ( sk_D_1 @ sk_A @ sk_B @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ~ ( r1_tarski @ ( sk_D_1 @ X11 @ X10 @ X9 ) @ X9 )
      | ( X9
        = ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('9',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ~ ( r1_tarski @ sk_A @ sk_A )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('11',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['12'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X12 ) @ X13 )
      | ~ ( r2_hidden @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ ( sk_C @ X15 @ X14 ) )
      | ( r1_tarski @ X15 @ ( k1_setfam_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('23',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QoaQeefY8M
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:07:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 38 iterations in 0.032s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(t7_setfam_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( r1_tarski @ A @ B ) =>
% 0.21/0.48          ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48            ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t7_setfam_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (~ (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t6_setfam_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.21/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i]:
% 0.21/0.48         (((X14) = (k1_xboole_0))
% 0.21/0.48          | (r2_hidden @ (sk_C @ X15 @ X14) @ X14)
% 0.21/0.48          | (r1_tarski @ X15 @ (k1_setfam_1 @ X14)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.21/0.48  thf(d10_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.48  thf('3', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.21/0.48      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.48  thf('4', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t20_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.48         ( ![D:$i]:
% 0.21/0.48           ( ( ( r1_tarski @ D @ B ) & ( r1_tarski @ D @ C ) ) =>
% 0.21/0.48             ( r1_tarski @ D @ A ) ) ) ) =>
% 0.21/0.48       ( ( A ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X9 @ X10)
% 0.21/0.48          | ~ (r1_tarski @ X9 @ X11)
% 0.21/0.48          | (r1_tarski @ (sk_D_1 @ X11 @ X10 @ X9) @ X11)
% 0.21/0.48          | ((X9) = (k3_xboole_0 @ X10 @ X11)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((sk_A) = (k3_xboole_0 @ sk_B @ X0))
% 0.21/0.48          | (r1_tarski @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.21/0.48          | ~ (r1_tarski @ sk_A @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (((r1_tarski @ (sk_D_1 @ sk_A @ sk_B @ sk_A) @ sk_A)
% 0.21/0.48        | ((sk_A) = (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X9 @ X10)
% 0.21/0.48          | ~ (r1_tarski @ X9 @ X11)
% 0.21/0.48          | ~ (r1_tarski @ (sk_D_1 @ X11 @ X10 @ X9) @ X9)
% 0.21/0.48          | ((X9) = (k3_xboole_0 @ X10 @ X11)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      ((((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.21/0.48        | ((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.21/0.48        | ~ (r1_tarski @ sk_A @ sk_A)
% 0.21/0.48        | ~ (r1_tarski @ sk_A @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.21/0.48      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.48  thf('11', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      ((((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.21/0.48        | ((sk_A) = (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.21/0.48  thf('13', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.48  thf(d4_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.48       ( ![D:$i]:
% 0.21/0.48         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.48           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.48          | (r2_hidden @ X4 @ X1)
% 0.21/0.48          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.48         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ X0 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.21/0.48          | ((sk_A) = (k1_xboole_0))
% 0.21/0.48          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '16'])).
% 0.21/0.48  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.21/0.48          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf(t4_setfam_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         ((r1_tarski @ (k1_setfam_1 @ X12) @ X13) | ~ (r2_hidden @ X13 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.21/0.48          | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (sk_C @ X0 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i]:
% 0.21/0.48         (((X14) = (k1_xboole_0))
% 0.21/0.48          | ~ (r1_tarski @ X15 @ (sk_C @ X15 @ X14))
% 0.21/0.48          | (r1_tarski @ X15 @ (k1_setfam_1 @ X14)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (((r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))
% 0.21/0.48        | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      ((((sk_A) = (k1_xboole_0))
% 0.21/0.48        | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.48  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('26', plain, ((r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.21/0.48  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
