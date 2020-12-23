%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gQq5Nf8dqa

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 (  73 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :   15
%              Number of atoms          :  333 ( 474 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t30_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_ordinal1])).

thf('0',plain,(
    ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( v1_ordinal1 @ X13 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r1_tarski @ X11 @ X12 )
      | ~ ( v1_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X3 ) @ X4 )
      | ~ ( r1_tarski @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X5 ) @ ( k3_tarski @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( k3_tarski @ X0 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X7 ) @ X8 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t56_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( sk_B @ ( k3_tarski @ X0 ) ) @ ( k3_tarski @ X0 ) )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X13: $i] :
      ( ( v1_ordinal1 @ X13 )
      | ~ ( r1_tarski @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( ( k3_tarski @ X0 )
        = X0 )
      | ( r2_xboole_0 @ ( k3_tarski @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ( r2_hidden @ X15 @ X14 )
      | ~ ( r2_xboole_0 @ X15 @ X14 )
      | ~ ( v1_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ X0 )
        = X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( ( k3_tarski @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ X0 )
        = X0 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v3_ordinal1 @ X16 )
      | ~ ( v3_ordinal1 @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( ( k3_tarski @ X0 )
        = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v3_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( ( k3_tarski @ X0 )
        = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( v1_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( ( k3_tarski @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('28',plain,(
    ! [X10: $i] :
      ( ( v1_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('29',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k3_tarski @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['26','29','30'])).

thf('32',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gQq5Nf8dqa
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:55:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 59 iterations in 0.071s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.56  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.20/0.56  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.56  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.56  thf(t30_ordinal1, conjecture,
% 0.20/0.56    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t30_ordinal1])).
% 0.20/0.56  thf('0', plain, (~ (v3_ordinal1 @ (k3_tarski @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d2_ordinal1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( v1_ordinal1 @ A ) <=>
% 0.20/0.56       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (![X13 : $i]: ((v1_ordinal1 @ X13) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.20/0.56  thf(t94_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.20/0.56       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X3 : $i, X4 : $i]:
% 0.20/0.56         ((r1_tarski @ (k3_tarski @ X3) @ X4)
% 0.20/0.56          | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.20/0.56      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X11 @ X12)
% 0.20/0.56          | (r1_tarski @ X11 @ X12)
% 0.20/0.56          | ~ (v1_ordinal1 @ X12))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.20/0.56          | ~ (v1_ordinal1 @ X0)
% 0.20/0.56          | (r1_tarski @ (sk_C @ X1 @ X0) @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (![X3 : $i, X4 : $i]:
% 0.20/0.56         ((r1_tarski @ (k3_tarski @ X3) @ X4)
% 0.20/0.56          | ~ (r1_tarski @ (sk_C @ X4 @ X3) @ X4))),
% 0.20/0.56      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (v1_ordinal1 @ X0)
% 0.20/0.56          | (r1_tarski @ (k3_tarski @ X0) @ X0)
% 0.20/0.56          | (r1_tarski @ (k3_tarski @ X0) @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X0 : $i]: ((r1_tarski @ (k3_tarski @ X0) @ X0) | ~ (v1_ordinal1 @ X0))),
% 0.20/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.56  thf(t95_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.56       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         ((r1_tarski @ (k3_tarski @ X5) @ (k3_tarski @ X6))
% 0.20/0.56          | ~ (r1_tarski @ X5 @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (v1_ordinal1 @ X0)
% 0.20/0.56          | (r1_tarski @ (k3_tarski @ (k3_tarski @ X0)) @ (k3_tarski @ X0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.56  thf(t56_setfam_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.20/0.56       ( r1_tarski @ C @ B ) ))).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.56         (~ (r1_tarski @ (k3_tarski @ X7) @ X8)
% 0.20/0.56          | ~ (r2_hidden @ X9 @ X7)
% 0.20/0.56          | (r1_tarski @ X9 @ X8))),
% 0.20/0.56      inference('cnf', [status(esa)], [t56_setfam_1])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (v1_ordinal1 @ X0)
% 0.20/0.56          | (r1_tarski @ X1 @ (k3_tarski @ X0))
% 0.20/0.56          | ~ (r2_hidden @ X1 @ (k3_tarski @ X0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v1_ordinal1 @ (k3_tarski @ X0))
% 0.20/0.56          | (r1_tarski @ (sk_B @ (k3_tarski @ X0)) @ (k3_tarski @ X0))
% 0.20/0.56          | ~ (v1_ordinal1 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '11'])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (![X13 : $i]: ((v1_ordinal1 @ X13) | ~ (r1_tarski @ (sk_B @ X13) @ X13))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (![X0 : $i]: (~ (v1_ordinal1 @ X0) | (v1_ordinal1 @ (k3_tarski @ X0)))),
% 0.20/0.56      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X0 : $i]: ((r1_tarski @ (k3_tarski @ X0) @ X0) | ~ (v1_ordinal1 @ X0))),
% 0.20/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.56  thf(d8_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.56       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X0 : $i, X2 : $i]:
% 0.20/0.56         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.56      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (v1_ordinal1 @ X0)
% 0.20/0.56          | ((k3_tarski @ X0) = (X0))
% 0.20/0.56          | (r2_xboole_0 @ (k3_tarski @ X0) @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.56  thf(t21_ordinal1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( v1_ordinal1 @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.56           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i]:
% 0.20/0.56         (~ (v3_ordinal1 @ X14)
% 0.20/0.56          | (r2_hidden @ X15 @ X14)
% 0.20/0.56          | ~ (r2_xboole_0 @ X15 @ X14)
% 0.20/0.56          | ~ (v1_ordinal1 @ X15))),
% 0.20/0.56      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k3_tarski @ X0) = (X0))
% 0.20/0.56          | ~ (v1_ordinal1 @ X0)
% 0.20/0.56          | ~ (v1_ordinal1 @ (k3_tarski @ X0))
% 0.20/0.56          | (r2_hidden @ (k3_tarski @ X0) @ X0)
% 0.20/0.56          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (v1_ordinal1 @ X0)
% 0.20/0.56          | ~ (v3_ordinal1 @ X0)
% 0.20/0.56          | (r2_hidden @ (k3_tarski @ X0) @ X0)
% 0.20/0.56          | ~ (v1_ordinal1 @ X0)
% 0.20/0.56          | ((k3_tarski @ X0) = (X0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['14', '19'])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k3_tarski @ X0) = (X0))
% 0.20/0.56          | (r2_hidden @ (k3_tarski @ X0) @ X0)
% 0.20/0.56          | ~ (v3_ordinal1 @ X0)
% 0.20/0.56          | ~ (v1_ordinal1 @ X0))),
% 0.20/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.56  thf(t23_ordinal1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X16 : $i, X17 : $i]:
% 0.20/0.56         ((v3_ordinal1 @ X16)
% 0.20/0.56          | ~ (v3_ordinal1 @ X17)
% 0.20/0.56          | ~ (r2_hidden @ X16 @ X17))),
% 0.20/0.56      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (v1_ordinal1 @ X0)
% 0.20/0.56          | ~ (v3_ordinal1 @ X0)
% 0.20/0.56          | ((k3_tarski @ X0) = (X0))
% 0.20/0.56          | ~ (v3_ordinal1 @ X0)
% 0.20/0.56          | (v3_ordinal1 @ (k3_tarski @ X0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v3_ordinal1 @ (k3_tarski @ X0))
% 0.20/0.56          | ((k3_tarski @ X0) = (X0))
% 0.20/0.56          | ~ (v3_ordinal1 @ X0)
% 0.20/0.56          | ~ (v1_ordinal1 @ X0))),
% 0.20/0.56      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.56  thf('25', plain, (~ (v3_ordinal1 @ (k3_tarski @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      ((~ (v1_ordinal1 @ sk_A)
% 0.20/0.56        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.56        | ((k3_tarski @ sk_A) = (sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.56  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(cc1_ordinal1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (![X10 : $i]: ((v1_ordinal1 @ X10) | ~ (v3_ordinal1 @ X10))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.20/0.56  thf('29', plain, ((v1_ordinal1 @ sk_A)),
% 0.20/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.56  thf('30', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('31', plain, (((k3_tarski @ sk_A) = (sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['26', '29', '30'])).
% 0.20/0.56  thf('32', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('33', plain, ($false),
% 0.20/0.56      inference('demod', [status(thm)], ['0', '31', '32'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
