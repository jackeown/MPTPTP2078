%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EFJWWrojoq

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:33 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  222 ( 285 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(t4_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t4_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X13: $i,X14: $i] :
      ( ( X10
       != ( k1_setfam_1 @ X11 ) )
      | ~ ( r2_hidden @ X13 @ X11 )
      | ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X14 @ X10 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('4',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r2_hidden @ X14 @ ( k1_setfam_1 @ X11 ) )
      | ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X13 @ X11 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_setfam_1 @ X0 ) ) @ X2 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_setfam_1 @ sk_B ) ) @ sk_A )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X11: $i,X16: $i] :
      ( ( X16
       != ( k1_setfam_1 @ X11 ) )
      | ( X16 = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('13',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['12'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','11','13','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EFJWWrojoq
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:42:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.34/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.55  % Solved by: fo/fo7.sh
% 0.34/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.55  % done 115 iterations in 0.106s
% 0.34/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.55  % SZS output start Refutation
% 0.34/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.34/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.34/0.55  thf(t4_setfam_1, conjecture,
% 0.34/0.55    (![A:$i,B:$i]:
% 0.34/0.55     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.34/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.55    (~( ![A:$i,B:$i]:
% 0.34/0.55        ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )),
% 0.34/0.55    inference('cnf.neg', [status(esa)], [t4_setfam_1])).
% 0.34/0.55  thf('0', plain, (~ (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A)),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf(d3_tarski, axiom,
% 0.34/0.55    (![A:$i,B:$i]:
% 0.34/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.34/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.34/0.55  thf('2', plain,
% 0.34/0.55      (![X1 : $i, X3 : $i]:
% 0.34/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.34/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.34/0.55  thf(d1_setfam_1, axiom,
% 0.34/0.55    (![A:$i,B:$i]:
% 0.34/0.55     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.34/0.55         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.34/0.55       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.34/0.55         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.34/0.55           ( ![C:$i]:
% 0.34/0.55             ( ( r2_hidden @ C @ B ) <=>
% 0.34/0.55               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.34/0.55  thf('3', plain,
% 0.34/0.55      (![X10 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 0.34/0.55         (((X10) != (k1_setfam_1 @ X11))
% 0.34/0.55          | ~ (r2_hidden @ X13 @ X11)
% 0.34/0.55          | (r2_hidden @ X14 @ X13)
% 0.34/0.55          | ~ (r2_hidden @ X14 @ X10)
% 0.34/0.55          | ((X11) = (k1_xboole_0)))),
% 0.34/0.55      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.34/0.55  thf('4', plain,
% 0.34/0.55      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.34/0.55         (((X11) = (k1_xboole_0))
% 0.34/0.55          | ~ (r2_hidden @ X14 @ (k1_setfam_1 @ X11))
% 0.34/0.55          | (r2_hidden @ X14 @ X13)
% 0.34/0.55          | ~ (r2_hidden @ X13 @ X11))),
% 0.34/0.55      inference('simplify', [status(thm)], ['3'])).
% 0.34/0.55  thf('5', plain,
% 0.34/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.55         ((r1_tarski @ (k1_setfam_1 @ X0) @ X1)
% 0.34/0.55          | ~ (r2_hidden @ X2 @ X0)
% 0.34/0.55          | (r2_hidden @ (sk_C @ X1 @ (k1_setfam_1 @ X0)) @ X2)
% 0.34/0.55          | ((X0) = (k1_xboole_0)))),
% 0.34/0.55      inference('sup-', [status(thm)], ['2', '4'])).
% 0.34/0.55  thf('6', plain,
% 0.34/0.55      (![X0 : $i]:
% 0.34/0.55         (((sk_B) = (k1_xboole_0))
% 0.34/0.55          | (r2_hidden @ (sk_C @ X0 @ (k1_setfam_1 @ sk_B)) @ sk_A)
% 0.34/0.55          | (r1_tarski @ (k1_setfam_1 @ sk_B) @ X0))),
% 0.34/0.55      inference('sup-', [status(thm)], ['1', '5'])).
% 0.34/0.55  thf('7', plain,
% 0.34/0.55      (![X1 : $i, X3 : $i]:
% 0.34/0.55         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.34/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.34/0.55  thf('8', plain,
% 0.34/0.55      (((r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A)
% 0.34/0.55        | ((sk_B) = (k1_xboole_0))
% 0.34/0.55        | (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A))),
% 0.34/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.34/0.55  thf('9', plain,
% 0.34/0.55      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A))),
% 0.34/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.34/0.55  thf('10', plain, (~ (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A)),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('11', plain, (((sk_B) = (k1_xboole_0))),
% 0.34/0.55      inference('clc', [status(thm)], ['9', '10'])).
% 0.34/0.55  thf('12', plain,
% 0.34/0.55      (![X11 : $i, X16 : $i]:
% 0.34/0.55         (((X16) != (k1_setfam_1 @ X11))
% 0.34/0.55          | ((X16) = (k1_xboole_0))
% 0.34/0.55          | ((X11) != (k1_xboole_0)))),
% 0.34/0.55      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.34/0.55  thf('13', plain, (((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.34/0.55  thf(t36_xboole_1, axiom,
% 0.34/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.34/0.55  thf('14', plain,
% 0.34/0.55      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.34/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.34/0.55  thf(t3_xboole_1, axiom,
% 0.34/0.55    (![A:$i]:
% 0.34/0.55     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.34/0.55  thf('15', plain,
% 0.34/0.55      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ k1_xboole_0))),
% 0.34/0.55      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.34/0.55  thf('16', plain,
% 0.34/0.55      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.34/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.34/0.55  thf(l32_xboole_1, axiom,
% 0.34/0.55    (![A:$i,B:$i]:
% 0.34/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.34/0.55  thf('17', plain,
% 0.34/0.55      (![X4 : $i, X5 : $i]:
% 0.34/0.55         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.34/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.34/0.55  thf('18', plain,
% 0.34/0.55      (![X0 : $i]:
% 0.34/0.55         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.34/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.34/0.55  thf('19', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.34/0.55      inference('simplify', [status(thm)], ['18'])).
% 0.34/0.55  thf('20', plain, ($false),
% 0.34/0.55      inference('demod', [status(thm)], ['0', '11', '13', '19'])).
% 0.34/0.55  
% 0.34/0.55  % SZS output end Refutation
% 0.34/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
