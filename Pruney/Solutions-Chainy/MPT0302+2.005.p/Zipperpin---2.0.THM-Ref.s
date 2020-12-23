%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZBLxOp4WT2

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 (  84 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  456 ( 700 expanded)
%              Number of equality atoms :   34 (  68 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7 = X6 )
      | ( r2_hidden @ ( sk_C_1 @ X6 @ X7 ) @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X6 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['5'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C_1 @ k1_xboole_0 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('10',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['17'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7 = X6 )
      | ( r2_hidden @ ( sk_C_1 @ X6 @ X7 ) @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X6 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(condensation,[status(thm)],['23'])).

thf('25',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( k1_xboole_0 = sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['37','38'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['20','41'])).

thf('43',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZBLxOp4WT2
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 102 iterations in 0.050s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(d3_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (![X3 : $i, X5 : $i]:
% 0.21/0.50         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf(t2_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.21/0.50       ( ( A ) = ( B ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]:
% 0.21/0.50         (((X7) = (X6))
% 0.21/0.50          | (r2_hidden @ (sk_C_1 @ X6 @ X7) @ X6)
% 0.21/0.50          | (r2_hidden @ (sk_C_1 @ X6 @ X7) @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_tarski])).
% 0.21/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.50  thf('2', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X2 @ X3)
% 0.21/0.50          | (r2_hidden @ X2 @ X4)
% 0.21/0.50          | ~ (r1_tarski @ X3 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.21/0.50          | ((X0) = (k1_xboole_0))
% 0.21/0.50          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.21/0.50          | ((X0) = (k1_xboole_0)))),
% 0.21/0.50      inference('condensation', [status(thm)], ['5'])).
% 0.21/0.50  thf(l54_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 0.21/0.50         ((r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X15))
% 0.21/0.50          | ~ (r2_hidden @ X13 @ X15)
% 0.21/0.50          | ~ (r2_hidden @ X11 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (((X0) = (k1_xboole_0))
% 0.21/0.50          | ~ (r2_hidden @ X2 @ X1)
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_1 @ k1_xboole_0 @ X0)) @ 
% 0.21/0.50             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((r1_tarski @ X0 @ X1)
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C_1 @ k1_xboole_0 @ X2)) @ 
% 0.21/0.50             (k2_zfmisc_1 @ X0 @ X2))
% 0.21/0.50          | ((X2) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '8'])).
% 0.21/0.50  thf(t114_zfmisc_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.21/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50         ( ( A ) = ( B ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.21/0.50          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50            ( ( A ) = ( B ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.51         ((r2_hidden @ X11 @ X12)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.51          | (r2_hidden @ X1 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((sk_B) = (k1_xboole_0))
% 0.21/0.51          | (r1_tarski @ sk_A @ X0)
% 0.21/0.51          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.51  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X3 : $i, X5 : $i]:
% 0.21/0.51         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('17', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('18', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.51      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.51  thf(t28_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.51  thf('20', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         (((X7) = (X6))
% 0.21/0.51          | (r2_hidden @ (sk_C_1 @ X6 @ X7) @ X6)
% 0.21/0.51          | (r2_hidden @ (sk_C_1 @ X6 @ X7) @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_tarski])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.51          | ((k1_xboole_0) = (X0))
% 0.21/0.51          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.51          | ((k1_xboole_0) = (X0)))),
% 0.21/0.51      inference('condensation', [status(thm)], ['23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X3 : $i, X5 : $i]:
% 0.21/0.51         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 0.21/0.51         ((r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X15))
% 0.21/0.51          | ~ (r2_hidden @ X13 @ X15)
% 0.21/0.51          | ~ (r2_hidden @ X11 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((r1_tarski @ X0 @ X1)
% 0.21/0.51          | ~ (r2_hidden @ X3 @ X2)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.21/0.51             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((k1_xboole_0) = (X0))
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ (sk_C @ X2 @ X1)) @ 
% 0.21/0.51             (k2_zfmisc_1 @ X0 @ X1))
% 0.21/0.51          | (r1_tarski @ X1 @ X2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['24', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.51         ((r2_hidden @ X13 @ X14)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.51          | (r2_hidden @ X0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r1_tarski @ sk_B @ X0)
% 0.21/0.51          | ((k1_xboole_0) = (sk_A))
% 0.21/0.51          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '31'])).
% 0.21/0.51  thf('33', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X3 : $i, X5 : $i]:
% 0.21/0.51         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('36', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.51  thf('37', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.51      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.51  thf('39', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.51  thf('41', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('42', plain, (((sk_A) = (sk_B))),
% 0.21/0.51      inference('sup+', [status(thm)], ['20', '41'])).
% 0.21/0.51  thf('43', plain, (((sk_A) != (sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('44', plain, ($false),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
