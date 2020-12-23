%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.49y1bOl1jV

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 123 expanded)
%              Number of leaves         :   18 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  410 (1053 expanded)
%              Number of equality atoms :   62 ( 163 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X25 ) @ ( k1_tarski @ X26 ) )
      | ( X25 = X26 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t20_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
      <=> ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t20_zfmisc_1])).

thf('3',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X17 != X16 )
      | ( r2_hidden @ X17 @ X18 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X16: $i] :
      ( r2_hidden @ X16 @ ( k1_tarski @ X16 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X23 ) @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t90_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) @ X15 ) ),
    inference(cnf,[status(esa)],[t90_xboole_1])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_B @ X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B ) ),
    inference('sup-',[status(thm)],['8','26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('29',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['6','27','28'])).

thf('30',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['4','29'])).

thf('31',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['2','30'])).

thf('32',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('34',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['6','27'])).

thf('35',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.49y1bOl1jV
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:49:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 128 iterations in 0.048s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(t17_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( A ) != ( B ) ) =>
% 0.20/0.51       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ (k1_tarski @ X25) @ (k1_tarski @ X26))
% 0.20/0.51          | ((X25) = (X26)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.20/0.51  thf(t83_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i]:
% 0.20/0.51         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X1) = (X0))
% 0.20/0.51          | ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.20/0.51              = (k1_tarski @ X1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf(t20_zfmisc_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.51         ( k1_tarski @ A ) ) <=>
% 0.20/0.51       ( ( A ) != ( B ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.51            ( k1_tarski @ A ) ) <=>
% 0.20/0.51          ( ( A ) != ( B ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      ((((sk_A) = (sk_B))
% 0.20/0.51        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51            != (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51          != (k1_tarski @ sk_A)))
% 0.20/0.51         <= (~
% 0.20/0.51             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51                = (k1_tarski @ sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['3'])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      ((((sk_A) != (sk_B))
% 0.20/0.51        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51            = (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (~ (((sk_A) = (sk_B))) | 
% 0.20/0.51       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51          = (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['5'])).
% 0.20/0.51  thf(d1_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.51         (((X17) != (X16))
% 0.20/0.51          | (r2_hidden @ X17 @ X18)
% 0.20/0.51          | ((X18) != (k1_tarski @ X16)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.51  thf('8', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_tarski @ X16))),
% 0.20/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.51  thf(d10_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.51  thf('10', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.51  thf(l32_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X3 : $i, X5 : $i]:
% 0.20/0.51         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.51  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['3'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51          = (k1_tarski @ sk_A)))
% 0.20/0.51         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51                = (k1_tarski @ sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['5'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.20/0.51          = (k1_tarski @ sk_A)))
% 0.20/0.51         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51                = (k1_tarski @ sk_A))) & 
% 0.20/0.51             (((sk_A) = (sk_B))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('16', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['3'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.20/0.51          = (k1_tarski @ sk_B)))
% 0.20/0.51         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51                = (k1_tarski @ sk_A))) & 
% 0.20/0.51             (((sk_A) = (sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((((k1_xboole_0) = (k1_tarski @ sk_B)))
% 0.20/0.51         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51                = (k1_tarski @ sk_A))) & 
% 0.20/0.51             (((sk_A) = (sk_B))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['12', '17'])).
% 0.20/0.51  thf(l24_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X23 : $i, X24 : $i]:
% 0.20/0.51         (~ (r1_xboole_0 @ (k1_tarski @ X23) @ X24) | ~ (r2_hidden @ X23 @ X24))),
% 0.20/0.51      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r2_hidden @ sk_B @ X0)))
% 0.20/0.51         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51                = (k1_tarski @ sk_A))) & 
% 0.20/0.51             (((sk_A) = (sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf(t90_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ))).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         (r1_xboole_0 @ (k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) @ X15)),
% 0.20/0.51      inference('cnf', [status(esa)], [t90_xboole_1])).
% 0.20/0.51  thf(t47_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.20/0.51           = (k4_xboole_0 @ X7 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 0.20/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('25', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.51      inference('sup+', [status(thm)], ['21', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((![X0 : $i]: ~ (r2_hidden @ sk_B @ X0))
% 0.20/0.51         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51                = (k1_tarski @ sk_A))) & 
% 0.20/0.51             (((sk_A) = (sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['20', '25'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (~
% 0.20/0.51       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51          = (k1_tarski @ sk_A))) | 
% 0.20/0.51       ~ (((sk_A) = (sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (~
% 0.20/0.51       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51          = (k1_tarski @ sk_A))) | 
% 0.20/0.51       (((sk_A) = (sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['3'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (~
% 0.20/0.51       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51          = (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['6', '27', '28'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51         != (k1_tarski @ sk_A))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['4', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | ((sk_A) = (sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '30'])).
% 0.20/0.51  thf('32', plain, (((sk_A) = (sk_B))),
% 0.20/0.51      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.51  thf('33', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['5'])).
% 0.20/0.51  thf('34', plain, (~ (((sk_A) = (sk_B)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['6', '27'])).
% 0.20/0.51  thf('35', plain, (((sk_A) != (sk_B))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['33', '34'])).
% 0.20/0.51  thf('36', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['32', '35'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
