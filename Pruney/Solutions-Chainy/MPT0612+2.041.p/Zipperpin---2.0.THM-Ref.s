%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A4oJi0wPxn

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:14 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  262 ( 332 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t211_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
       => ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) )
          = ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k6_subset_1 @ X12 @ ( k7_relat_1 @ X12 @ X14 ) )
        = ( k7_relat_1 @ X12 @ ( k6_subset_1 @ X13 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t211_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k4_xboole_0 @ X12 @ ( k7_relat_1 @ X12 @ X14 ) )
        = ( k7_relat_1 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X2 ) )
        = ( k7_relat_1 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(t216_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t216_relat_1])).

thf('6',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_xboole_0 @ X4 @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X11 @ X9 ) @ X10 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ ( k4_xboole_0 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ( k7_relat_1 @ ( k6_subset_1 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ( k7_relat_1 @ ( k4_xboole_0 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A4oJi0wPxn
% 0.13/0.37  % Computer   : n022.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 16:37:26 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 28 iterations in 0.023s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.23/0.50  thf(t7_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.23/0.50  thf('0', plain,
% 0.23/0.50      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 0.23/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.23/0.50  thf(t211_relat_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ C ) =>
% 0.23/0.50       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 0.23/0.50         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 0.23/0.50           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.23/0.50         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.23/0.50          | ((k6_subset_1 @ X12 @ (k7_relat_1 @ X12 @ X14))
% 0.23/0.50              = (k7_relat_1 @ X12 @ (k6_subset_1 @ X13 @ X14)))
% 0.23/0.50          | ~ (v1_relat_1 @ X12))),
% 0.23/0.50      inference('cnf', [status(esa)], [t211_relat_1])).
% 0.23/0.50  thf(redefinition_k6_subset_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      (![X7 : $i, X8 : $i]: ((k6_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))),
% 0.23/0.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (![X7 : $i, X8 : $i]: ((k6_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))),
% 0.23/0.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.23/0.50  thf('4', plain,
% 0.23/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.23/0.50         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.23/0.50          | ((k4_xboole_0 @ X12 @ (k7_relat_1 @ X12 @ X14))
% 0.23/0.50              = (k7_relat_1 @ X12 @ (k4_xboole_0 @ X13 @ X14)))
% 0.23/0.50          | ~ (v1_relat_1 @ X12))),
% 0.23/0.50      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.23/0.50  thf('5', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.50         (~ (v1_relat_1 @ X1)
% 0.23/0.50          | ((k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X2))
% 0.23/0.50              = (k7_relat_1 @ X1 @ 
% 0.23/0.50                 (k4_xboole_0 @ (k2_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2))))),
% 0.23/0.50      inference('sup-', [status(thm)], ['0', '4'])).
% 0.23/0.50  thf(t216_relat_1, conjecture,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ C ) =>
% 0.23/0.50       ( ( r1_tarski @ A @ B ) =>
% 0.23/0.50         ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.23/0.50           ( k1_xboole_0 ) ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.50        ( ( v1_relat_1 @ C ) =>
% 0.23/0.50          ( ( r1_tarski @ A @ B ) =>
% 0.23/0.50            ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.23/0.50              ( k1_xboole_0 ) ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t216_relat_1])).
% 0.23/0.50  thf('6', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(t85_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.23/0.50  thf('7', plain,
% 0.23/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.50         (~ (r1_tarski @ X4 @ X5)
% 0.23/0.50          | (r1_xboole_0 @ X4 @ (k4_xboole_0 @ X6 @ X5)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.23/0.50  thf('8', plain,
% 0.23/0.50      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.23/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.50  thf(symmetry_r1_xboole_0, axiom,
% 0.23/0.50    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.23/0.50  thf('9', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.23/0.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)),
% 0.23/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.50  thf(t207_relat_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ C ) =>
% 0.23/0.50       ( ( r1_xboole_0 @ A @ B ) =>
% 0.23/0.50         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.50  thf('11', plain,
% 0.23/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.23/0.50         (~ (r1_xboole_0 @ X9 @ X10)
% 0.23/0.50          | ~ (v1_relat_1 @ X11)
% 0.23/0.50          | ((k7_relat_1 @ (k7_relat_1 @ X11 @ X9) @ X10) = (k1_xboole_0)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (((k7_relat_1 @ (k7_relat_1 @ X1 @ (k4_xboole_0 @ X0 @ sk_B)) @ sk_A)
% 0.23/0.50            = (k1_xboole_0))
% 0.23/0.50          | ~ (v1_relat_1 @ X1))),
% 0.23/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.23/0.50            = (k1_xboole_0))
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0))),
% 0.23/0.50      inference('sup+', [status(thm)], ['5', '12'])).
% 0.23/0.50  thf('14', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (~ (v1_relat_1 @ X0)
% 0.23/0.50          | ((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.23/0.50              = (k1_xboole_0)))),
% 0.23/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.23/0.50  thf('15', plain,
% 0.23/0.50      (((k7_relat_1 @ (k6_subset_1 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 0.23/0.50         != (k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('16', plain,
% 0.23/0.50      (![X7 : $i, X8 : $i]: ((k6_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))),
% 0.23/0.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.23/0.50  thf('17', plain,
% 0.23/0.50      (((k7_relat_1 @ (k4_xboole_0 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 0.23/0.50         != (k1_xboole_0))),
% 0.23/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.23/0.50  thf('18', plain,
% 0.23/0.50      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C))),
% 0.23/0.50      inference('sup-', [status(thm)], ['14', '17'])).
% 0.23/0.50  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('20', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.23/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.23/0.50  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
