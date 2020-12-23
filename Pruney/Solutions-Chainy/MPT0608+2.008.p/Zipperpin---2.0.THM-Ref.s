%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9Ff2dGnbHZ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  52 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  312 ( 405 expanded)
%              Number of equality atoms :   29 (  40 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(t211_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
       => ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) )
          = ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k6_subset_1 @ X11 @ ( k7_relat_1 @ X11 @ X13 ) )
        = ( k7_relat_1 @ X11 @ ( k6_subset_1 @ X12 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t211_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k6_subset_1 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ ( k6_subset_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k6_subset_1 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ ( k6_subset_1 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ ( k6_subset_1 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k6_subset_1 @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k6_subset_1 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
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

thf('20',plain,
    ( ( ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9Ff2dGnbHZ
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:58:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 16 iterations in 0.016s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.48  thf(d10_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.48  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.48      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.48  thf(t211_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ C ) =>
% 0.21/0.48       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 0.21/0.48         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 0.21/0.48           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.48         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.21/0.48          | ((k6_subset_1 @ X11 @ (k7_relat_1 @ X11 @ X13))
% 0.21/0.48              = (k7_relat_1 @ X11 @ (k6_subset_1 @ X12 @ X13)))
% 0.21/0.48          | ~ (v1_relat_1 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t211_relat_1])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | ((k6_subset_1 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 0.21/0.48              = (k7_relat_1 @ X0 @ (k6_subset_1 @ (k1_relat_1 @ X0) @ X1))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf(t90_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.21/0.48         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i]:
% 0.21/0.48         (((k1_relat_1 @ (k7_relat_1 @ X14 @ X15))
% 0.21/0.48            = (k3_xboole_0 @ (k1_relat_1 @ X14) @ X15))
% 0.21/0.48          | ~ (v1_relat_1 @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k1_relat_1 @ (k6_subset_1 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.48            = (k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.21/0.48               (k6_subset_1 @ (k1_relat_1 @ X1) @ X0)))
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | ~ (v1_relat_1 @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf(t48_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.21/0.48           = (k3_xboole_0 @ X7 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.48  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         ((k6_subset_1 @ X7 @ (k6_subset_1 @ X7 @ X8))
% 0.21/0.48           = (k3_xboole_0 @ X7 @ X8))),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         ((k6_subset_1 @ X7 @ (k6_subset_1 @ X7 @ X8))
% 0.21/0.48           = (k3_xboole_0 @ X7 @ X8))),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.48           = (k3_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf(t47_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6))
% 0.21/0.48           = (k4_xboole_0 @ X5 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         ((k6_subset_1 @ X5 @ (k3_xboole_0 @ X5 @ X6))
% 0.21/0.48           = (k6_subset_1 @ X5 @ X6))),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k3_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0))
% 0.21/0.48           = (k6_subset_1 @ X1 @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['11', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k1_relat_1 @ (k6_subset_1 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.48            = (k6_subset_1 @ (k1_relat_1 @ X1) @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | ~ (v1_relat_1 @ X1))),
% 0.21/0.48      inference('demod', [status(thm)], ['5', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X1)
% 0.21/0.48          | ((k1_relat_1 @ (k6_subset_1 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.48              = (k6_subset_1 @ (k1_relat_1 @ X1) @ X0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.48  thf(t212_relat_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.21/0.48         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( v1_relat_1 @ B ) =>
% 0.21/0.48          ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.21/0.48            ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t212_relat_1])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (((k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.21/0.48         != (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((((k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.48          != (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.48         != (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
