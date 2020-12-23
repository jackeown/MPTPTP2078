%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sP2POORJXx

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  42 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  163 ( 215 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(rc1_relat_1,axiom,(
    ? [A: $i] :
      ( ( v1_relat_1 @ A )
      & ~ ( v1_xboole_0 @ A ) ) )).

thf('0',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_relat_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t41_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) )
            = ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k4_relat_1 @ ( k6_subset_1 @ X7 @ X6 ) )
        = ( k6_subset_1 @ ( k4_relat_1 @ X7 ) @ ( k4_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t41_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ X4 @ X5 )
      = ( k4_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ X4 @ X5 )
      = ( k4_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k4_relat_1 @ ( k4_xboole_0 @ X7 @ X6 ) )
        = ( k4_xboole_0 @ ( k4_relat_1 @ X7 ) @ ( k4_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t66_relat_1,conjecture,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k4_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t66_relat_1])).

thf('13',plain,(
    ( k4_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( v1_relat_1 @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['11','14'])).

thf('16',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sP2POORJXx
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:34:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 17 iterations in 0.014s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(rc1_relat_1, axiom,
% 0.21/0.47    (?[A:$i]: ( ( v1_relat_1 @ A ) & ( ~( v1_xboole_0 @ A ) ) ))).
% 0.21/0.47  thf('0', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [rc1_relat_1])).
% 0.21/0.47  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.47  thf('1', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.47  thf(t100_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i]:
% 0.21/0.47         ((k4_xboole_0 @ X1 @ X2)
% 0.21/0.47           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(t92_xboole_1, axiom,
% 0.21/0.47    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.47  thf('4', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.47  thf('5', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf(t41_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( v1_relat_1 @ B ) =>
% 0.21/0.47           ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) ) =
% 0.21/0.47             ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X6)
% 0.21/0.47          | ((k4_relat_1 @ (k6_subset_1 @ X7 @ X6))
% 0.21/0.47              = (k6_subset_1 @ (k4_relat_1 @ X7) @ (k4_relat_1 @ X6)))
% 0.21/0.47          | ~ (v1_relat_1 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [t41_relat_1])).
% 0.21/0.47  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]: ((k6_subset_1 @ X4 @ X5) = (k4_xboole_0 @ X4 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]: ((k6_subset_1 @ X4 @ X5) = (k4_xboole_0 @ X4 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X6)
% 0.21/0.47          | ((k4_relat_1 @ (k4_xboole_0 @ X7 @ X6))
% 0.21/0.47              = (k4_xboole_0 @ (k4_relat_1 @ X7) @ (k4_relat_1 @ X6)))
% 0.21/0.47          | ~ (v1_relat_1 @ X7))),
% 0.21/0.47      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['5', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.47  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf(t66_relat_1, conjecture,
% 0.21/0.47    (( k4_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (( k4_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t66_relat_1])).
% 0.21/0.47  thf('13', plain, (((k4_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i]: ((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) != (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain, (![X0 : $i]: ~ (v1_relat_1 @ X0)),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['11', '14'])).
% 0.21/0.47  thf('16', plain, ($false), inference('sup-', [status(thm)], ['0', '15'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
