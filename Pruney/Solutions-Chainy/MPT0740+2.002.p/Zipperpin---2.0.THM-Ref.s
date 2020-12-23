%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RS138PLPYD

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 (  73 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :   15
%              Number of atoms          :  330 ( 471 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

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
    ! [X14: $i] :
      ( ( v1_ordinal1 @ X14 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X9 ) @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( r1_tarski @ X12 @ X13 )
      | ~ ( v1_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X9 ) @ X10 )
      | ~ ( r1_tarski @ ( sk_C_1 @ X10 @ X9 ) @ X10 ) ) ),
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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ ( k3_tarski @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( sk_B @ ( k3_tarski @ X0 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X14: $i] :
      ( ( v1_ordinal1 @ X14 )
      | ~ ( r1_tarski @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
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
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_xboole_0 @ X16 @ X15 )
      | ~ ( v1_ordinal1 @ X16 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
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
    ! [X11: $i] :
      ( ( v1_ordinal1 @ X11 )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
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
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RS138PLPYD
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:44:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 60 iterations in 0.046s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.22/0.51  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.22/0.51  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.22/0.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.22/0.51  thf(t30_ordinal1, conjecture,
% 0.22/0.51    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t30_ordinal1])).
% 0.22/0.51  thf('0', plain, (~ (v3_ordinal1 @ (k3_tarski @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d2_ordinal1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_ordinal1 @ A ) <=>
% 0.22/0.51       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (![X14 : $i]: ((v1_ordinal1 @ X14) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.22/0.51      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.22/0.51  thf(t94_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.22/0.51       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X9 : $i, X10 : $i]:
% 0.22/0.51         ((r1_tarski @ (k3_tarski @ X9) @ X10)
% 0.22/0.51          | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ X9))),
% 0.22/0.51      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X12 : $i, X13 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X12 @ X13)
% 0.22/0.51          | (r1_tarski @ X12 @ X13)
% 0.22/0.51          | ~ (v1_ordinal1 @ X13))),
% 0.22/0.51      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.22/0.51          | ~ (v1_ordinal1 @ X0)
% 0.22/0.51          | (r1_tarski @ (sk_C_1 @ X1 @ X0) @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X9 : $i, X10 : $i]:
% 0.22/0.51         ((r1_tarski @ (k3_tarski @ X9) @ X10)
% 0.22/0.51          | ~ (r1_tarski @ (sk_C_1 @ X10 @ X9) @ X10))),
% 0.22/0.51      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_ordinal1 @ X0)
% 0.22/0.51          | (r1_tarski @ (k3_tarski @ X0) @ X0)
% 0.22/0.51          | (r1_tarski @ (k3_tarski @ X0) @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X0 : $i]: ((r1_tarski @ (k3_tarski @ X0) @ X0) | ~ (v1_ordinal1 @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.51  thf(d3_tarski, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.51          | (r2_hidden @ X0 @ X2)
% 0.22/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (v1_ordinal1 @ X0)
% 0.22/0.51          | (r2_hidden @ X1 @ X0)
% 0.22/0.51          | ~ (r2_hidden @ X1 @ (k3_tarski @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v1_ordinal1 @ (k3_tarski @ X0))
% 0.22/0.51          | (r2_hidden @ (sk_B @ (k3_tarski @ X0)) @ X0)
% 0.22/0.51          | ~ (v1_ordinal1 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '9'])).
% 0.22/0.51  thf(l49_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i]:
% 0.22/0.51         ((r1_tarski @ X7 @ (k3_tarski @ X8)) | ~ (r2_hidden @ X7 @ X8))),
% 0.22/0.51      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_ordinal1 @ X0)
% 0.22/0.51          | (v1_ordinal1 @ (k3_tarski @ X0))
% 0.22/0.51          | (r1_tarski @ (sk_B @ (k3_tarski @ X0)) @ (k3_tarski @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X14 : $i]: ((v1_ordinal1 @ X14) | ~ (r1_tarski @ (sk_B @ X14) @ X14))),
% 0.22/0.51      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X0 : $i]: ((v1_ordinal1 @ (k3_tarski @ X0)) | ~ (v1_ordinal1 @ X0))),
% 0.22/0.51      inference('clc', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X0 : $i]: ((r1_tarski @ (k3_tarski @ X0) @ X0) | ~ (v1_ordinal1 @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.51  thf(d8_xboole_0, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.22/0.51       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X4 : $i, X6 : $i]:
% 0.22/0.51         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_ordinal1 @ X0)
% 0.22/0.51          | ((k3_tarski @ X0) = (X0))
% 0.22/0.51          | (r2_xboole_0 @ (k3_tarski @ X0) @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf(t21_ordinal1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_ordinal1 @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.51           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X15 : $i, X16 : $i]:
% 0.22/0.51         (~ (v3_ordinal1 @ X15)
% 0.22/0.51          | (r2_hidden @ X16 @ X15)
% 0.22/0.51          | ~ (r2_xboole_0 @ X16 @ X15)
% 0.22/0.51          | ~ (v1_ordinal1 @ X16))),
% 0.22/0.51      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((k3_tarski @ X0) = (X0))
% 0.22/0.51          | ~ (v1_ordinal1 @ X0)
% 0.22/0.51          | ~ (v1_ordinal1 @ (k3_tarski @ X0))
% 0.22/0.51          | (r2_hidden @ (k3_tarski @ X0) @ X0)
% 0.22/0.51          | ~ (v3_ordinal1 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_ordinal1 @ X0)
% 0.22/0.51          | ~ (v3_ordinal1 @ X0)
% 0.22/0.51          | (r2_hidden @ (k3_tarski @ X0) @ X0)
% 0.22/0.51          | ~ (v1_ordinal1 @ X0)
% 0.22/0.51          | ((k3_tarski @ X0) = (X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['14', '19'])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((k3_tarski @ X0) = (X0))
% 0.22/0.51          | (r2_hidden @ (k3_tarski @ X0) @ X0)
% 0.22/0.51          | ~ (v3_ordinal1 @ X0)
% 0.22/0.51          | ~ (v1_ordinal1 @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.51  thf(t23_ordinal1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X17 : $i, X18 : $i]:
% 0.22/0.51         ((v3_ordinal1 @ X17)
% 0.22/0.51          | ~ (v3_ordinal1 @ X18)
% 0.22/0.51          | ~ (r2_hidden @ X17 @ X18))),
% 0.22/0.51      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_ordinal1 @ X0)
% 0.22/0.51          | ~ (v3_ordinal1 @ X0)
% 0.22/0.51          | ((k3_tarski @ X0) = (X0))
% 0.22/0.51          | ~ (v3_ordinal1 @ X0)
% 0.22/0.51          | (v3_ordinal1 @ (k3_tarski @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v3_ordinal1 @ (k3_tarski @ X0))
% 0.22/0.51          | ((k3_tarski @ X0) = (X0))
% 0.22/0.51          | ~ (v3_ordinal1 @ X0)
% 0.22/0.51          | ~ (v1_ordinal1 @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.51  thf('25', plain, (~ (v3_ordinal1 @ (k3_tarski @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      ((~ (v1_ordinal1 @ sk_A)
% 0.22/0.51        | ~ (v3_ordinal1 @ sk_A)
% 0.22/0.51        | ((k3_tarski @ sk_A) = (sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.51  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(cc1_ordinal1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      (![X11 : $i]: ((v1_ordinal1 @ X11) | ~ (v3_ordinal1 @ X11))),
% 0.22/0.51      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.22/0.51  thf('29', plain, ((v1_ordinal1 @ sk_A)),
% 0.22/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.51  thf('30', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('31', plain, (((k3_tarski @ sk_A) = (sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['26', '29', '30'])).
% 0.22/0.51  thf('32', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('33', plain, ($false),
% 0.22/0.51      inference('demod', [status(thm)], ['0', '31', '32'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
