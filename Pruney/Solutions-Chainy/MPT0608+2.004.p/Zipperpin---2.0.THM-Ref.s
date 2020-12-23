%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.avTGrKcFG7

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:57 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   46 (  51 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  355 ( 402 expanded)
%              Number of equality atoms :   32 (  37 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('2',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X53 ) @ X54 )
      | ( ( k7_relat_1 @ X53 @ X54 )
        = X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k7_relat_1 @ X46 @ ( k6_subset_1 @ X47 @ X48 ) )
        = ( k6_subset_1 @ ( k7_relat_1 @ X46 @ X47 ) @ ( k7_relat_1 @ X46 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t109_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k7_relat_1 @ X46 @ ( k4_xboole_0 @ X47 @ X48 ) )
        = ( k4_xboole_0 @ ( k7_relat_1 @ X46 @ X47 ) @ ( k7_relat_1 @ X46 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
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

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X49 @ X50 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X49 ) @ X50 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

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

thf('19',plain,(
    ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.avTGrKcFG7
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 230 iterations in 0.140s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.59  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.37/0.59  thf(d10_xboole_0, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.59  thf('0', plain,
% 0.37/0.59      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.59  thf('1', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.37/0.59      inference('simplify', [status(thm)], ['0'])).
% 0.37/0.59  thf(t97_relat_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( v1_relat_1 @ B ) =>
% 0.37/0.59       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.37/0.59         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.37/0.59  thf('2', plain,
% 0.37/0.59      (![X53 : $i, X54 : $i]:
% 0.37/0.59         (~ (r1_tarski @ (k1_relat_1 @ X53) @ X54)
% 0.37/0.59          | ((k7_relat_1 @ X53 @ X54) = (X53))
% 0.37/0.59          | ~ (v1_relat_1 @ X53))),
% 0.37/0.59      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.37/0.59  thf('3', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.59  thf(t109_relat_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( v1_relat_1 @ C ) =>
% 0.37/0.59       ( ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.37/0.59         ( k6_subset_1 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.37/0.59  thf('4', plain,
% 0.37/0.59      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.37/0.59         (((k7_relat_1 @ X46 @ (k6_subset_1 @ X47 @ X48))
% 0.37/0.59            = (k6_subset_1 @ (k7_relat_1 @ X46 @ X47) @ 
% 0.37/0.59               (k7_relat_1 @ X46 @ X48)))
% 0.37/0.59          | ~ (v1_relat_1 @ X46))),
% 0.37/0.59      inference('cnf', [status(esa)], [t109_relat_1])).
% 0.37/0.59  thf(redefinition_k6_subset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      (![X40 : $i, X41 : $i]:
% 0.37/0.59         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.37/0.59  thf('6', plain,
% 0.37/0.59      (![X40 : $i, X41 : $i]:
% 0.37/0.59         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.37/0.59  thf('7', plain,
% 0.37/0.59      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.37/0.59         (((k7_relat_1 @ X46 @ (k4_xboole_0 @ X47 @ X48))
% 0.37/0.59            = (k4_xboole_0 @ (k7_relat_1 @ X46 @ X47) @ 
% 0.37/0.59               (k7_relat_1 @ X46 @ X48)))
% 0.37/0.59          | ~ (v1_relat_1 @ X46))),
% 0.37/0.59      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.37/0.59  thf('8', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (((k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 0.37/0.59            = (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1)))
% 0.37/0.60          | ~ (v1_relat_1 @ X0)
% 0.37/0.60          | ~ (v1_relat_1 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['3', '7'])).
% 0.37/0.60  thf('9', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (~ (v1_relat_1 @ X0)
% 0.37/0.60          | ((k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 0.37/0.60              = (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))))),
% 0.37/0.60      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.60  thf(t90_relat_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ B ) =>
% 0.37/0.60       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.37/0.60         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.37/0.60  thf('10', plain,
% 0.37/0.60      (![X49 : $i, X50 : $i]:
% 0.37/0.60         (((k1_relat_1 @ (k7_relat_1 @ X49 @ X50))
% 0.37/0.60            = (k3_xboole_0 @ (k1_relat_1 @ X49) @ X50))
% 0.37/0.60          | ~ (v1_relat_1 @ X49))),
% 0.37/0.60      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.37/0.60  thf('11', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.37/0.60            = (k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.37/0.60               (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 0.37/0.60          | ~ (v1_relat_1 @ X1)
% 0.37/0.60          | ~ (v1_relat_1 @ X1))),
% 0.37/0.60      inference('sup+', [status(thm)], ['9', '10'])).
% 0.37/0.60  thf(t36_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.60  thf('12', plain,
% 0.37/0.60      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.37/0.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.60  thf(t28_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.60  thf('13', plain,
% 0.37/0.60      (![X9 : $i, X10 : $i]:
% 0.37/0.60         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.37/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.60  thf('14', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.37/0.60           = (k4_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.60  thf('15', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.60  thf('16', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.37/0.60           = (k4_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.60  thf('17', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.37/0.60            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.37/0.60          | ~ (v1_relat_1 @ X1)
% 0.37/0.60          | ~ (v1_relat_1 @ X1))),
% 0.37/0.60      inference('demod', [status(thm)], ['11', '16'])).
% 0.37/0.60  thf('18', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (~ (v1_relat_1 @ X1)
% 0.37/0.60          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.37/0.60              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['17'])).
% 0.37/0.60  thf(t212_relat_1, conjecture,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ B ) =>
% 0.37/0.60       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.37/0.60         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.37/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.60    (~( ![A:$i,B:$i]:
% 0.37/0.60        ( ( v1_relat_1 @ B ) =>
% 0.37/0.60          ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.37/0.60            ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.37/0.60    inference('cnf.neg', [status(esa)], [t212_relat_1])).
% 0.37/0.60  thf('19', plain,
% 0.37/0.60      (((k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.37/0.60         != (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('20', plain,
% 0.37/0.60      (![X40 : $i, X41 : $i]:
% 0.37/0.60         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.37/0.60  thf('21', plain,
% 0.37/0.60      (![X40 : $i, X41 : $i]:
% 0.37/0.60         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.37/0.60  thf('22', plain,
% 0.37/0.60      (((k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.37/0.60         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.37/0.60      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.37/0.60  thf('23', plain,
% 0.37/0.60      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.37/0.60          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.37/0.60        | ~ (v1_relat_1 @ sk_B))),
% 0.37/0.60      inference('sup-', [status(thm)], ['18', '22'])).
% 0.37/0.60  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('25', plain,
% 0.37/0.60      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.37/0.60         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.37/0.60      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.60  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.37/0.60  
% 0.37/0.60  % SZS output end Refutation
% 0.37/0.60  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
