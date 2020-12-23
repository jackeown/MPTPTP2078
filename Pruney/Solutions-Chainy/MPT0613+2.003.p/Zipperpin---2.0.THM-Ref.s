%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mqLTWC3bM4

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:15 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 (  97 expanded)
%              Number of leaves         :   13 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  297 ( 761 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t217_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A ) )
         => ( v4_relat_1 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v4_relat_1 @ C @ A ) )
           => ( v4_relat_1 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t217_relat_1])).

thf('0',plain,(
    ~ ( v4_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v4_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) @ X4 )
      | ~ ( v4_relat_1 @ X3 @ X5 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( v4_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      | ( ( k7_relat_1 @ sk_C @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) )
      | ~ ( v4_relat_1 @ X3 @ X5 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_C @ X0 )
      = ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t104_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k7_relat_1 @ X8 @ X6 ) @ ( k7_relat_1 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t104_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_A ) @ ( k7_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('24',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['17','22','23','24','25'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X11 @ X12 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('34',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mqLTWC3bM4
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 57 iterations in 0.106s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.53  thf(t217_relat_1, conjecture,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( r1_tarski @ A @ B ) =>
% 0.19/0.53       ( ![C:$i]:
% 0.19/0.53         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 0.19/0.53           ( v4_relat_1 @ C @ B ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i,B:$i]:
% 0.19/0.53        ( ( r1_tarski @ A @ B ) =>
% 0.19/0.53          ( ![C:$i]:
% 0.19/0.53            ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 0.19/0.53              ( v4_relat_1 @ C @ B ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t217_relat_1])).
% 0.19/0.53  thf('0', plain, (~ (v4_relat_1 @ sk_C @ sk_B)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('1', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(fc23_relat_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ B ) ) =>
% 0.19/0.53       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 0.19/0.53         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A ) & 
% 0.19/0.53         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         ((v4_relat_1 @ (k7_relat_1 @ X3 @ X4) @ X4)
% 0.19/0.53          | ~ (v4_relat_1 @ X3 @ X5)
% 0.19/0.53          | ~ (v1_relat_1 @ X3))),
% 0.19/0.53      inference('cnf', [status(esa)], [fc23_relat_1])).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ sk_C) | (v4_relat_1 @ (k7_relat_1 @ sk_C @ X0) @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.53  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('5', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_C @ X0) @ X0)),
% 0.19/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.53  thf(t209_relat_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.19/0.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      (![X9 : $i, X10 : $i]:
% 0.19/0.53         (((X9) = (k7_relat_1 @ X9 @ X10))
% 0.19/0.53          | ~ (v4_relat_1 @ X9 @ X10)
% 0.19/0.53          | ~ (v1_relat_1 @ X9))),
% 0.19/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ X0))
% 0.19/0.53          | ((k7_relat_1 @ sk_C @ X0)
% 0.19/0.53              = (k7_relat_1 @ (k7_relat_1 @ sk_C @ X0) @ X0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.53  thf('8', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         ((v1_relat_1 @ (k7_relat_1 @ X3 @ X4))
% 0.19/0.53          | ~ (v4_relat_1 @ X3 @ X5)
% 0.19/0.53          | ~ (v1_relat_1 @ X3))),
% 0.19/0.53      inference('cnf', [status(esa)], [fc23_relat_1])).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ sk_C) | (v1_relat_1 @ (k7_relat_1 @ sk_C @ X0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.53  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('12', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_C @ X0))),
% 0.19/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k7_relat_1 @ sk_C @ X0)
% 0.19/0.53           = (k7_relat_1 @ (k7_relat_1 @ sk_C @ X0) @ X0))),
% 0.19/0.53      inference('demod', [status(thm)], ['7', '12'])).
% 0.19/0.53  thf('14', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(t104_relat_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ C ) =>
% 0.19/0.53       ( ( r1_tarski @ A @ B ) =>
% 0.19/0.53         ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.53         (~ (r1_tarski @ X6 @ X7)
% 0.19/0.53          | ~ (v1_relat_1 @ X8)
% 0.19/0.53          | (r1_tarski @ (k7_relat_1 @ X8 @ X6) @ (k7_relat_1 @ X8 @ X7)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t104_relat_1])).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ (k7_relat_1 @ X0 @ sk_B))
% 0.19/0.53          | ~ (v1_relat_1 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      (((r1_tarski @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.19/0.53         (k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B))
% 0.19/0.53        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['13', '16'])).
% 0.19/0.53  thf('18', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      (![X9 : $i, X10 : $i]:
% 0.19/0.53         (((X9) = (k7_relat_1 @ X9 @ X10))
% 0.19/0.53          | ~ (v4_relat_1 @ X9 @ X10)
% 0.19/0.53          | ~ (v1_relat_1 @ X9))),
% 0.19/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.53  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('22', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.53  thf('23', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.53  thf('24', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.53  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('26', plain, ((r1_tarski @ sk_C @ (k7_relat_1 @ sk_C @ sk_B))),
% 0.19/0.53      inference('demod', [status(thm)], ['17', '22', '23', '24', '25'])).
% 0.19/0.53  thf(t88_relat_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.19/0.53  thf('27', plain,
% 0.19/0.53      (![X11 : $i, X12 : $i]:
% 0.19/0.53         ((r1_tarski @ (k7_relat_1 @ X11 @ X12) @ X11) | ~ (v1_relat_1 @ X11))),
% 0.19/0.53      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.19/0.53  thf(d10_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.53  thf('28', plain,
% 0.19/0.53      (![X0 : $i, X2 : $i]:
% 0.19/0.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.53  thf('29', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X0)
% 0.19/0.53          | ~ (r1_tarski @ X0 @ (k7_relat_1 @ X0 @ X1))
% 0.19/0.53          | ((X0) = (k7_relat_1 @ X0 @ X1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.53  thf('30', plain,
% 0.19/0.53      ((((sk_C) = (k7_relat_1 @ sk_C @ sk_B)) | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.53      inference('sup-', [status(thm)], ['26', '29'])).
% 0.19/0.53  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('32', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.19/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.19/0.53  thf('33', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_C @ X0) @ X0)),
% 0.19/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.53  thf('34', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.19/0.53      inference('sup+', [status(thm)], ['32', '33'])).
% 0.19/0.53  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
