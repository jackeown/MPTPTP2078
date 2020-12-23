%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fF7qf36T1e

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   18 (  20 expanded)
%              Number of leaves         :    8 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   81 (  97 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( ( k7_relat_1 @ X3 @ X4 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t98_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t98_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    $false ),
    inference(simplify,[status(thm)],['7'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fF7qf36T1e
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 6 iterations in 0.009s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.47  thf(d10_xboole_0, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.47  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.47      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.47  thf(t97_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ B ) =>
% 0.22/0.47       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.22/0.47         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i]:
% 0.22/0.47         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.22/0.47          | ((k7_relat_1 @ X3 @ X4) = (X3))
% 0.22/0.47          | ~ (v1_relat_1 @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.47  thf(t98_relat_1, conjecture,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ A ) =>
% 0.22/0.47       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]:
% 0.22/0.47        ( ( v1_relat_1 @ A ) =>
% 0.22/0.47          ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t98_relat_1])).
% 0.22/0.47  thf('4', plain, (((k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)) != (sk_A))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('5', plain, ((((sk_A) != (sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.47  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('7', plain, (((sk_A) != (sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.47  thf('8', plain, ($false), inference('simplify', [status(thm)], ['7'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
