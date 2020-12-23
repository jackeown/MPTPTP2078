%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sCYJAU1Txb

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:34 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   43 (  48 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  265 ( 320 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X30 != X29 )
      | ( r2_hidden @ X30 @ X31 )
      | ( X31
       != ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X29: $i] :
      ( r2_hidden @ X29 @ ( k1_tarski @ X29 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X5 ) )
      | ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('17',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X44 ) @ X45 )
      | ~ ( r2_hidden @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X32 @ X31 )
      | ( X32 = X29 )
      | ( X31
       != ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('21',plain,(
    ! [X29: $i,X32: $i] :
      ( ( X32 = X29 )
      | ~ ( r2_hidden @ X32 @ ( k1_tarski @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    sk_A = sk_B_1 ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sCYJAU1Txb
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 221 iterations in 0.132s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.58  thf(t18_zfmisc_1, conjecture,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.58         ( k1_tarski @ A ) ) =>
% 0.38/0.58       ( ( A ) = ( B ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i,B:$i]:
% 0.38/0.58        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.58            ( k1_tarski @ A ) ) =>
% 0.38/0.58          ( ( A ) = ( B ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.38/0.58  thf('0', plain,
% 0.38/0.58      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58         = (k1_tarski @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (((k3_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.38/0.58         = (k1_tarski @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.38/0.58  thf(t100_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (![X11 : $i, X12 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X11 @ X12)
% 0.38/0.58           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      (((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.38/0.58         = (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.58  thf(d1_tarski, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.58  thf('5', plain,
% 0.38/0.58      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.58         (((X30) != (X29))
% 0.38/0.58          | (r2_hidden @ X30 @ X31)
% 0.38/0.58          | ((X31) != (k1_tarski @ X29)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.58  thf('6', plain, (![X29 : $i]: (r2_hidden @ X29 @ (k1_tarski @ X29))),
% 0.38/0.58      inference('simplify', [status(thm)], ['5'])).
% 0.38/0.58  thf(t1_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.38/0.58       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.38/0.58         ((r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X5))
% 0.38/0.58          | (r2_hidden @ X2 @ X3)
% 0.38/0.58          | ~ (r2_hidden @ X2 @ X5))),
% 0.38/0.58      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((r2_hidden @ X0 @ X1)
% 0.38/0.58          | (r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.58  thf('9', plain,
% 0.38/0.58      (((r2_hidden @ sk_A @ 
% 0.38/0.58         (k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A)))
% 0.38/0.58        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['4', '8'])).
% 0.38/0.58  thf(t79_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 0.38/0.58      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.38/0.58  thf(t4_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.38/0.58            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (![X6 : $i, X7 : $i]:
% 0.38/0.58         ((r1_xboole_0 @ X6 @ X7)
% 0.38/0.58          | (r2_hidden @ (sk_C @ X7 @ X6) @ (k3_xboole_0 @ X6 @ X7)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.38/0.58          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.38/0.58      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.58          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['11', '14'])).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['10', '15'])).
% 0.38/0.58  thf(l24_zfmisc_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      (![X44 : $i, X45 : $i]:
% 0.38/0.58         (~ (r1_xboole_0 @ (k1_tarski @ X44) @ X45) | ~ (r2_hidden @ X44 @ X45))),
% 0.38/0.58      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.58  thf('19', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.38/0.58      inference('clc', [status(thm)], ['9', '18'])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X29 : $i, X31 : $i, X32 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X32 @ X31)
% 0.38/0.58          | ((X32) = (X29))
% 0.38/0.58          | ((X31) != (k1_tarski @ X29)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (![X29 : $i, X32 : $i]:
% 0.38/0.58         (((X32) = (X29)) | ~ (r2_hidden @ X32 @ (k1_tarski @ X29)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['20'])).
% 0.38/0.58  thf('22', plain, (((sk_A) = (sk_B_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['19', '21'])).
% 0.38/0.58  thf('23', plain, (((sk_A) != (sk_B_1))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('24', plain, ($false),
% 0.38/0.58      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
