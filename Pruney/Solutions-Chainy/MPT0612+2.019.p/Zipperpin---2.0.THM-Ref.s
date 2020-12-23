%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P2TZQM0LQD

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:11 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   50 (  59 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  335 ( 428 expanded)
%              Number of equality atoms :   28 (  36 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

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
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ( ( k7_relat_1 @ X17 @ X18 )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ X11 @ ( k6_subset_1 @ X12 @ X13 ) )
        = ( k6_subset_1 @ ( k7_relat_1 @ X11 @ X12 ) @ ( k7_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t109_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
        = ( k4_xboole_0 @ ( k7_relat_1 @ X11 @ X12 ) @ ( k7_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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

thf('10',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_xboole_0 @ X6 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_xboole_0 @ X6 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X16 @ X14 ) @ X15 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ ( k4_xboole_0 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ( k7_relat_1 @ ( k6_subset_1 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('25',plain,(
    ( k7_relat_1 @ ( k4_xboole_0 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P2TZQM0LQD
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 209 iterations in 0.109s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.56  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.37/0.56  thf(d10_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.56  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.56      inference('simplify', [status(thm)], ['0'])).
% 0.37/0.56  thf(t97_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ B ) =>
% 0.37/0.56       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.37/0.56         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i]:
% 0.37/0.56         (~ (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.37/0.56          | ((k7_relat_1 @ X17 @ X18) = (X17))
% 0.37/0.56          | ~ (v1_relat_1 @ X17))),
% 0.37/0.56      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.56  thf(t109_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ C ) =>
% 0.37/0.56       ( ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.37/0.56         ( k6_subset_1 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.56         (((k7_relat_1 @ X11 @ (k6_subset_1 @ X12 @ X13))
% 0.37/0.56            = (k6_subset_1 @ (k7_relat_1 @ X11 @ X12) @ 
% 0.37/0.56               (k7_relat_1 @ X11 @ X13)))
% 0.37/0.56          | ~ (v1_relat_1 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t109_relat_1])).
% 0.37/0.56  thf(redefinition_k6_subset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i]:
% 0.37/0.56         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i]:
% 0.37/0.56         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.56         (((k7_relat_1 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.37/0.56            = (k4_xboole_0 @ (k7_relat_1 @ X11 @ X12) @ 
% 0.37/0.56               (k7_relat_1 @ X11 @ X13)))
% 0.37/0.56          | ~ (v1_relat_1 @ X11))),
% 0.37/0.56      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 0.37/0.56            = (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1)))
% 0.37/0.56          | ~ (v1_relat_1 @ X0)
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['3', '7'])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | ((k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 0.37/0.56              = (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.56  thf(t216_relat_1, conjecture,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ C ) =>
% 0.37/0.56       ( ( r1_tarski @ A @ B ) =>
% 0.37/0.56         ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.37/0.56           ( k1_xboole_0 ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.56        ( ( v1_relat_1 @ C ) =>
% 0.37/0.56          ( ( r1_tarski @ A @ B ) =>
% 0.37/0.56            ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.37/0.56              ( k1_xboole_0 ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t216_relat_1])).
% 0.37/0.56  thf('10', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t85_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X6 @ X7)
% 0.37/0.56          | (r1_xboole_0 @ X6 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.56  thf(t83_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X3 : $i, X4 : $i]:
% 0.37/0.56         (((k4_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 0.37/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X0 : $i]: ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)) = (sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.56  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.56      inference('simplify', [status(thm)], ['0'])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X6 @ X7)
% 0.37/0.56          | (r1_xboole_0 @ X6 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)),
% 0.37/0.56      inference('sup+', [status(thm)], ['14', '17'])).
% 0.37/0.56  thf(t207_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ C ) =>
% 0.37/0.56       ( ( r1_xboole_0 @ A @ B ) =>
% 0.37/0.56         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.56         (~ (r1_xboole_0 @ X14 @ X15)
% 0.37/0.56          | ~ (v1_relat_1 @ X16)
% 0.37/0.56          | ((k7_relat_1 @ (k7_relat_1 @ X16 @ X14) @ X15) = (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((k7_relat_1 @ (k7_relat_1 @ X1 @ (k4_xboole_0 @ X0 @ sk_B)) @ sk_A)
% 0.37/0.56            = (k1_xboole_0))
% 0.37/0.56          | ~ (v1_relat_1 @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.37/0.56            = (k1_xboole_0))
% 0.37/0.56          | ~ (v1_relat_1 @ X0)
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['9', '20'])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | ((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.37/0.56              = (k1_xboole_0)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (((k7_relat_1 @ (k6_subset_1 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 0.37/0.56         != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i]:
% 0.37/0.56         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (((k7_relat_1 @ (k4_xboole_0 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 0.37/0.56         != (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C))),
% 0.37/0.56      inference('sup-', [status(thm)], ['22', '25'])).
% 0.37/0.56  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('28', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['26', '27'])).
% 0.37/0.56  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
