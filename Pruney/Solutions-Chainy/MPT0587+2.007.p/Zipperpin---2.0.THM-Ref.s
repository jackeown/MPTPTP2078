%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.upd4TpNXkA

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  173 ( 208 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t191_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) )
          = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t191_relat_1])).

thf('6',plain,(
    ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
 != ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.upd4TpNXkA
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 18 iterations in 0.011s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.44  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(d10_xboole_0, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.44  thf('0', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.44  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.44      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.44  thf(t109_xboole_1, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.20/0.44  thf('2', plain,
% 0.20/0.44      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.44         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k4_xboole_0 @ X3 @ X5) @ X4))),
% 0.20/0.44      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.20/0.44  thf('3', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.44      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.44  thf(t91_relat_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( v1_relat_1 @ B ) =>
% 0.20/0.44       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.44         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.20/0.44  thf('4', plain,
% 0.20/0.44      (![X8 : $i, X9 : $i]:
% 0.20/0.44         (~ (r1_tarski @ X8 @ (k1_relat_1 @ X9))
% 0.20/0.44          | ((k1_relat_1 @ (k7_relat_1 @ X9 @ X8)) = (X8))
% 0.20/0.44          | ~ (v1_relat_1 @ X9))),
% 0.20/0.44      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.20/0.44  thf('5', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]:
% 0.20/0.44         (~ (v1_relat_1 @ X0)
% 0.20/0.44          | ((k1_relat_1 @ 
% 0.20/0.44              (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1)))
% 0.20/0.44              = (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.44  thf(t191_relat_1, conjecture,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( v1_relat_1 @ B ) =>
% 0.20/0.44       ( ( k1_relat_1 @
% 0.20/0.44           ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) =
% 0.20/0.44         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i,B:$i]:
% 0.20/0.44        ( ( v1_relat_1 @ B ) =>
% 0.20/0.44          ( ( k1_relat_1 @
% 0.20/0.44              ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) =
% 0.20/0.44            ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t191_relat_1])).
% 0.20/0.44  thf('6', plain,
% 0.20/0.44      (((k1_relat_1 @ 
% 0.20/0.44         (k7_relat_1 @ sk_B @ (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.20/0.44         != (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.44  thf('7', plain,
% 0.20/0.44      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.20/0.44      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.44  thf('8', plain,
% 0.20/0.44      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.20/0.44      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.44  thf('9', plain,
% 0.20/0.44      (((k1_relat_1 @ 
% 0.20/0.44         (k7_relat_1 @ sk_B @ (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.20/0.44         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.44      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.44  thf('10', plain,
% 0.20/0.44      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.20/0.44          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.20/0.44        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.44      inference('sup-', [status(thm)], ['5', '9'])).
% 0.20/0.44  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('12', plain,
% 0.20/0.44      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.20/0.44         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.44      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.44  thf('13', plain, ($false), inference('simplify', [status(thm)], ['12'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
