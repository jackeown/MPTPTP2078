%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uTpPsDN1oq

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  305 ( 352 expanded)
%              Number of equality atoms :   26 (  31 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X49 ) @ X50 )
      | ( ( k7_relat_1 @ X49 @ X50 )
        = X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t109_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('4',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k7_relat_1 @ X42 @ ( k6_subset_1 @ X43 @ X44 ) )
        = ( k6_subset_1 @ ( k7_relat_1 @ X42 @ X43 ) @ ( k7_relat_1 @ X42 @ X44 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t109_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k6_subset_1 @ X36 @ X37 )
      = ( k4_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k6_subset_1 @ X36 @ X37 )
      = ( k4_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k7_relat_1 @ X42 @ ( k4_xboole_0 @ X43 @ X44 ) )
        = ( k4_xboole_0 @ ( k7_relat_1 @ X42 @ X43 ) @ ( k7_relat_1 @ X42 @ X44 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('11',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ X47 @ ( k1_relat_1 @ X48 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X48 @ X47 ) )
        = X47 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t212_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
          = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t212_relat_1])).

thf('15',plain,(
    ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k6_subset_1 @ X36 @ X37 )
      = ( k4_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k6_subset_1 @ X36 @ X37 )
      = ( k4_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('18',plain,(
    ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uTpPsDN1oq
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:36:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 98 iterations in 0.056s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.51  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(d10_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.51  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.51      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.51  thf(t97_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.21/0.51         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X49 : $i, X50 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k1_relat_1 @ X49) @ X50)
% 0.21/0.51          | ((k7_relat_1 @ X49 @ X50) = (X49))
% 0.21/0.51          | ~ (v1_relat_1 @ X49))),
% 0.21/0.51      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf(t109_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ C ) =>
% 0.21/0.51       ( ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.21/0.51         ( k6_subset_1 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.21/0.51         (((k7_relat_1 @ X42 @ (k6_subset_1 @ X43 @ X44))
% 0.21/0.51            = (k6_subset_1 @ (k7_relat_1 @ X42 @ X43) @ 
% 0.21/0.51               (k7_relat_1 @ X42 @ X44)))
% 0.21/0.51          | ~ (v1_relat_1 @ X42))),
% 0.21/0.51      inference('cnf', [status(esa)], [t109_relat_1])).
% 0.21/0.51  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X36 : $i, X37 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X36 : $i, X37 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.21/0.51         (((k7_relat_1 @ X42 @ (k4_xboole_0 @ X43 @ X44))
% 0.21/0.51            = (k4_xboole_0 @ (k7_relat_1 @ X42 @ X43) @ 
% 0.21/0.51               (k7_relat_1 @ X42 @ X44)))
% 0.21/0.51          | ~ (v1_relat_1 @ X42))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 0.21/0.51            = (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1)))
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['3', '7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | ((k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 0.21/0.51              = (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.51  thf(t36_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.21/0.51      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.51  thf(t91_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.51         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X47 : $i, X48 : $i]:
% 0.21/0.51         (~ (r1_tarski @ X47 @ (k1_relat_1 @ X48))
% 0.21/0.51          | ((k1_relat_1 @ (k7_relat_1 @ X48 @ X47)) = (X47))
% 0.21/0.51          | ~ (v1_relat_1 @ X48))),
% 0.21/0.51      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | ((k1_relat_1 @ 
% 0.21/0.51              (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1)))
% 0.21/0.51              = (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.51            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['9', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X1)
% 0.21/0.51          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.51              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.51  thf(t212_relat_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.21/0.51         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ( v1_relat_1 @ B ) =>
% 0.21/0.51          ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.21/0.51            ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t212_relat_1])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (((k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.21/0.51         != (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X36 : $i, X37 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X36 : $i, X37 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (((k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.21/0.51         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.51          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.21/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '18'])).
% 0.21/0.51  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.51         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
