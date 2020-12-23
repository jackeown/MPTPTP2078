%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2TellaUPZd

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:42 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   12 (  19 expanded)
%              Depth                    :   12
%              Number of atoms          :  291 ( 377 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t79_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t79_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( r1_tarski @ X15 @ X13 )
      | ( X14
       != ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_tarski @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ X1 )
      | ( ( k3_xboole_0 @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
        = ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('12',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ( X14
       != ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','22'])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,
    ( ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2TellaUPZd
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.54/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.73  % Solved by: fo/fo7.sh
% 0.54/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.73  % done 517 iterations in 0.279s
% 0.54/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.73  % SZS output start Refutation
% 0.54/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.54/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.73  thf(t79_zfmisc_1, conjecture,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r1_tarski @ A @ B ) =>
% 0.54/0.73       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.54/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.73    (~( ![A:$i,B:$i]:
% 0.54/0.73        ( ( r1_tarski @ A @ B ) =>
% 0.54/0.73          ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )),
% 0.54/0.73    inference('cnf.neg', [status(esa)], [t79_zfmisc_1])).
% 0.54/0.73  thf('0', plain,
% 0.54/0.73      (~ (r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(d3_tarski, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r1_tarski @ A @ B ) <=>
% 0.54/0.73       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.54/0.73  thf('1', plain,
% 0.54/0.73      (![X1 : $i, X3 : $i]:
% 0.54/0.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.73  thf(d1_zfmisc_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.54/0.73       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.54/0.73  thf('2', plain,
% 0.54/0.73      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.54/0.73         (~ (r2_hidden @ X15 @ X14)
% 0.54/0.73          | (r1_tarski @ X15 @ X13)
% 0.54/0.73          | ((X14) != (k1_zfmisc_1 @ X13)))),
% 0.54/0.73      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.54/0.73  thf('3', plain,
% 0.54/0.73      (![X13 : $i, X15 : $i]:
% 0.54/0.73         ((r1_tarski @ X15 @ X13) | ~ (r2_hidden @ X15 @ (k1_zfmisc_1 @ X13)))),
% 0.54/0.73      inference('simplify', [status(thm)], ['2'])).
% 0.54/0.73  thf('4', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((r1_tarski @ (k1_zfmisc_1 @ X0) @ X1)
% 0.54/0.73          | (r1_tarski @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['1', '3'])).
% 0.54/0.73  thf(t28_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.54/0.73  thf('5', plain,
% 0.54/0.73      (![X10 : $i, X11 : $i]:
% 0.54/0.73         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.54/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.54/0.73  thf('6', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((r1_tarski @ (k1_zfmisc_1 @ X0) @ X1)
% 0.54/0.73          | ((k3_xboole_0 @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X0)
% 0.54/0.73              = (sk_C @ X1 @ (k1_zfmisc_1 @ X0))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.73  thf('7', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('8', plain,
% 0.54/0.73      (![X10 : $i, X11 : $i]:
% 0.54/0.73         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.54/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.54/0.73  thf('9', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.54/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.54/0.73  thf('10', plain,
% 0.54/0.73      (![X1 : $i, X3 : $i]:
% 0.54/0.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.73  thf(d4_xboole_0, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.54/0.73       ( ![D:$i]:
% 0.54/0.73         ( ( r2_hidden @ D @ C ) <=>
% 0.54/0.73           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.54/0.73  thf('11', plain,
% 0.54/0.73      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.54/0.73         (~ (r2_hidden @ X8 @ X7)
% 0.54/0.73          | (r2_hidden @ X8 @ X6)
% 0.54/0.73          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.54/0.73      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.54/0.73  thf('12', plain,
% 0.54/0.73      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.54/0.73         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.54/0.73      inference('simplify', [status(thm)], ['11'])).
% 0.54/0.73  thf('13', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.54/0.73          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['10', '12'])).
% 0.54/0.73  thf('14', plain,
% 0.54/0.73      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.54/0.73         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.54/0.73      inference('simplify', [status(thm)], ['11'])).
% 0.54/0.73  thf('15', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.73         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 0.54/0.73          | (r2_hidden @ 
% 0.54/0.73             (sk_C @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['13', '14'])).
% 0.54/0.73  thf('16', plain,
% 0.54/0.73      (![X1 : $i, X3 : $i]:
% 0.54/0.73         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.73  thf('17', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 0.54/0.73          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['15', '16'])).
% 0.54/0.73  thf('18', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0)),
% 0.54/0.73      inference('simplify', [status(thm)], ['17'])).
% 0.54/0.73  thf('19', plain,
% 0.54/0.73      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B)),
% 0.54/0.73      inference('sup+', [status(thm)], ['9', '18'])).
% 0.54/0.73  thf('20', plain,
% 0.54/0.73      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.54/0.73         (~ (r1_tarski @ X12 @ X13)
% 0.54/0.73          | (r2_hidden @ X12 @ X14)
% 0.54/0.73          | ((X14) != (k1_zfmisc_1 @ X13)))),
% 0.54/0.73      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.54/0.73  thf('21', plain,
% 0.54/0.73      (![X12 : $i, X13 : $i]:
% 0.54/0.73         ((r2_hidden @ X12 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X12 @ X13))),
% 0.54/0.73      inference('simplify', [status(thm)], ['20'])).
% 0.54/0.73  thf('22', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (r2_hidden @ (k3_xboole_0 @ X0 @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 0.54/0.73      inference('sup-', [status(thm)], ['19', '21'])).
% 0.54/0.73  thf('23', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r2_hidden @ (sk_C @ X0 @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.54/0.73           (k1_zfmisc_1 @ sk_B))
% 0.54/0.73          | (r1_tarski @ (k1_zfmisc_1 @ sk_A) @ X0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['6', '22'])).
% 0.54/0.73  thf('24', plain,
% 0.54/0.73      (![X1 : $i, X3 : $i]:
% 0.54/0.73         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.73  thf('25', plain,
% 0.54/0.73      (((r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 0.54/0.73        | (r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['23', '24'])).
% 0.54/0.73  thf('26', plain, ((r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 0.54/0.73      inference('simplify', [status(thm)], ['25'])).
% 0.54/0.73  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.54/0.73  
% 0.54/0.73  % SZS output end Refutation
% 0.54/0.73  
% 0.54/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
