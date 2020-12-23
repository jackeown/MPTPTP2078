%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fxCOGOiSm1

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:55 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   22 (  28 expanded)
%              Number of leaves         :   10 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   95 ( 155 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t209_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v4_relat_1 @ B @ A ) )
       => ( B
          = ( k7_relat_1 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t209_relat_1])).

thf('0',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['2','3'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ( ( k7_relat_1 @ X2 @ X3 )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    sk_B
 != ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fxCOGOiSm1
% 0.17/0.39  % Computer   : n025.cluster.edu
% 0.17/0.39  % Model      : x86_64 x86_64
% 0.17/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.39  % Memory     : 8042.1875MB
% 0.17/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.39  % CPULimit   : 60
% 0.17/0.39  % DateTime   : Tue Dec  1 12:13:51 EST 2020
% 0.17/0.39  % CPUTime    : 
% 0.17/0.39  % Running portfolio for 600 s
% 0.17/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.39  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.25/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.50  % Solved by: fo/fo7.sh
% 0.25/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.50  % done 6 iterations in 0.006s
% 0.25/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.50  % SZS output start Refutation
% 0.25/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.25/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.25/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.25/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.25/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.50  thf(t209_relat_1, conjecture,
% 0.25/0.50    (![A:$i,B:$i]:
% 0.25/0.50     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.25/0.50       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.25/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.50    (~( ![A:$i,B:$i]:
% 0.25/0.50        ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.25/0.50          ( ( B ) = ( k7_relat_1 @ B @ A ) ) ) )),
% 0.25/0.50    inference('cnf.neg', [status(esa)], [t209_relat_1])).
% 0.25/0.50  thf('0', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.25/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.50  thf(d18_relat_1, axiom,
% 0.25/0.50    (![A:$i,B:$i]:
% 0.25/0.50     ( ( v1_relat_1 @ B ) =>
% 0.25/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.25/0.50  thf('1', plain,
% 0.25/0.50      (![X0 : $i, X1 : $i]:
% 0.25/0.50         (~ (v4_relat_1 @ X0 @ X1)
% 0.25/0.50          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.25/0.50          | ~ (v1_relat_1 @ X0))),
% 0.25/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.25/0.50  thf('2', plain,
% 0.25/0.50      ((~ (v1_relat_1 @ sk_B) | (r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.25/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.25/0.50  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.25/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.50  thf('4', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.25/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.25/0.50  thf(t97_relat_1, axiom,
% 0.25/0.50    (![A:$i,B:$i]:
% 0.25/0.50     ( ( v1_relat_1 @ B ) =>
% 0.25/0.50       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.25/0.50         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.25/0.50  thf('5', plain,
% 0.25/0.50      (![X2 : $i, X3 : $i]:
% 0.25/0.50         (~ (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.25/0.50          | ((k7_relat_1 @ X2 @ X3) = (X2))
% 0.25/0.50          | ~ (v1_relat_1 @ X2))),
% 0.25/0.50      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.25/0.50  thf('6', plain,
% 0.25/0.50      ((~ (v1_relat_1 @ sk_B) | ((k7_relat_1 @ sk_B @ sk_A) = (sk_B)))),
% 0.25/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.25/0.50  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.25/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.50  thf('8', plain, (((k7_relat_1 @ sk_B @ sk_A) = (sk_B))),
% 0.25/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.25/0.50  thf('9', plain, (((sk_B) != (k7_relat_1 @ sk_B @ sk_A))),
% 0.25/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.50  thf('10', plain, ($false),
% 0.25/0.50      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.25/0.50  
% 0.25/0.50  % SZS output end Refutation
% 0.25/0.50  
% 0.25/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
