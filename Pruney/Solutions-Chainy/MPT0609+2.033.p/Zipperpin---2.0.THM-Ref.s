%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V6MGY9dFJ7

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:03 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  336 ( 389 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( ( ( k7_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t103_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X15 @ X14 ) @ X13 )
        = ( k7_relat_1 @ X15 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(t212_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X16 @ ( k7_relat_1 @ X16 @ X17 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t212_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X16 @ ( k7_relat_1 @ X16 @ X17 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t213_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k6_subset_1 @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) )
        = ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k6_subset_1 @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) )
          = ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t213_relat_1])).

thf('14',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V6MGY9dFJ7
% 0.18/0.37  % Computer   : n012.cluster.edu
% 0.18/0.37  % Model      : x86_64 x86_64
% 0.18/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.18/0.37  % Memory     : 8042.1875MB
% 0.18/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.37  % CPULimit   : 60
% 0.18/0.37  % DateTime   : Tue Dec  1 16:13:07 EST 2020
% 0.18/0.37  % CPUTime    : 
% 0.18/0.37  % Running portfolio for 600 s
% 0.18/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.38  % Number of cores: 8
% 0.18/0.38  % Python version: Python 3.6.8
% 0.18/0.38  % Running in FO mode
% 0.35/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.52  % Solved by: fo/fo7.sh
% 0.35/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.52  % done 45 iterations in 0.039s
% 0.35/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.52  % SZS output start Refutation
% 0.35/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.52  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.35/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.35/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.52  thf(t98_relat_1, axiom,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ A ) =>
% 0.35/0.52       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.35/0.52  thf('0', plain,
% 0.35/0.52      (![X20 : $i]:
% 0.35/0.52         (((k7_relat_1 @ X20 @ (k1_relat_1 @ X20)) = (X20))
% 0.35/0.52          | ~ (v1_relat_1 @ X20))),
% 0.35/0.52      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.35/0.52  thf(t87_relat_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ B ) =>
% 0.35/0.52       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.35/0.52  thf('1', plain,
% 0.35/0.52      (![X18 : $i, X19 : $i]:
% 0.35/0.52         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X18 @ X19)) @ X19)
% 0.35/0.52          | ~ (v1_relat_1 @ X18))),
% 0.35/0.52      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.35/0.52  thf(t103_relat_1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ C ) =>
% 0.35/0.52       ( ( r1_tarski @ A @ B ) =>
% 0.35/0.52         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.35/0.52  thf('2', plain,
% 0.35/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.35/0.52         (~ (r1_tarski @ X13 @ X14)
% 0.35/0.52          | ~ (v1_relat_1 @ X15)
% 0.35/0.52          | ((k7_relat_1 @ (k7_relat_1 @ X15 @ X14) @ X13)
% 0.35/0.52              = (k7_relat_1 @ X15 @ X13)))),
% 0.35/0.52      inference('cnf', [status(esa)], [t103_relat_1])).
% 0.35/0.52  thf('3', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X1)
% 0.35/0.52          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ 
% 0.35/0.52              (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.35/0.52              = (k7_relat_1 @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.35/0.52          | ~ (v1_relat_1 @ X2))),
% 0.35/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.52  thf('4', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (((k7_relat_1 @ X1 @ X0)
% 0.35/0.52            = (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.35/0.52          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.35/0.52          | ~ (v1_relat_1 @ X1)
% 0.35/0.52          | ~ (v1_relat_1 @ X1))),
% 0.35/0.52      inference('sup+', [status(thm)], ['0', '3'])).
% 0.35/0.52  thf('5', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X1)
% 0.35/0.52          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.35/0.52          | ((k7_relat_1 @ X1 @ X0)
% 0.35/0.52              = (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 0.35/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.35/0.52  thf(dt_k7_relat_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.35/0.52  thf('6', plain,
% 0.35/0.52      (![X11 : $i, X12 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 0.35/0.52      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.35/0.52  thf('7', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (((k7_relat_1 @ X1 @ X0)
% 0.35/0.52            = (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.35/0.52          | ~ (v1_relat_1 @ X1))),
% 0.35/0.52      inference('clc', [status(thm)], ['5', '6'])).
% 0.35/0.52  thf(t212_relat_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ B ) =>
% 0.35/0.52       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.35/0.52         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.35/0.52  thf('8', plain,
% 0.35/0.52      (![X16 : $i, X17 : $i]:
% 0.35/0.52         (((k1_relat_1 @ (k6_subset_1 @ X16 @ (k7_relat_1 @ X16 @ X17)))
% 0.35/0.52            = (k6_subset_1 @ (k1_relat_1 @ X16) @ X17))
% 0.35/0.52          | ~ (v1_relat_1 @ X16))),
% 0.35/0.52      inference('cnf', [status(esa)], [t212_relat_1])).
% 0.35/0.52  thf(redefinition_k6_subset_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.35/0.52  thf('9', plain,
% 0.35/0.52      (![X7 : $i, X8 : $i]: ((k6_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))),
% 0.35/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.35/0.52  thf('10', plain,
% 0.35/0.52      (![X7 : $i, X8 : $i]: ((k6_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))),
% 0.35/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.35/0.52  thf('11', plain,
% 0.35/0.52      (![X16 : $i, X17 : $i]:
% 0.35/0.52         (((k1_relat_1 @ (k4_xboole_0 @ X16 @ (k7_relat_1 @ X16 @ X17)))
% 0.35/0.52            = (k4_xboole_0 @ (k1_relat_1 @ X16) @ X17))
% 0.35/0.52          | ~ (v1_relat_1 @ X16))),
% 0.35/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.35/0.52  thf('12', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.35/0.52            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.35/0.52               (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.35/0.52          | ~ (v1_relat_1 @ X1)
% 0.35/0.52          | ~ (v1_relat_1 @ X1))),
% 0.35/0.52      inference('sup+', [status(thm)], ['7', '11'])).
% 0.35/0.52  thf('13', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X1)
% 0.35/0.52          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.35/0.52              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.35/0.52                 (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 0.35/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.35/0.52  thf(t213_relat_1, conjecture,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ B ) =>
% 0.35/0.52       ( ( k6_subset_1 @
% 0.35/0.52           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.35/0.52         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 0.35/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.52    (~( ![A:$i,B:$i]:
% 0.35/0.52        ( ( v1_relat_1 @ B ) =>
% 0.35/0.52          ( ( k6_subset_1 @
% 0.35/0.52              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.35/0.52            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 0.35/0.52    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 0.35/0.52  thf('14', plain,
% 0.35/0.52      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.35/0.52         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.35/0.52         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('15', plain,
% 0.35/0.52      (![X7 : $i, X8 : $i]: ((k6_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))),
% 0.35/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.35/0.52  thf('16', plain,
% 0.35/0.52      (![X7 : $i, X8 : $i]: ((k6_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))),
% 0.35/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.35/0.52  thf('17', plain,
% 0.35/0.52      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.35/0.52         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.35/0.52         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.35/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.35/0.52  thf('18', plain,
% 0.35/0.52      ((((k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.35/0.52          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.35/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.35/0.52      inference('sup-', [status(thm)], ['13', '17'])).
% 0.35/0.52  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('20', plain,
% 0.35/0.52      (((k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.35/0.52         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.35/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.35/0.52  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.35/0.52  
% 0.35/0.52  % SZS output end Refutation
% 0.35/0.52  
% 0.38/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
