%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TuNciIoC9f

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:49 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   34 (  42 expanded)
%              Number of leaves         :   14 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  181 ( 235 expanded)
%              Number of equality atoms :   24 (  32 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t136_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k8_relat_1 @ ( k6_subset_1 @ A @ B ) @ C )
        = ( k6_subset_1 @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k8_relat_1 @ ( k6_subset_1 @ X20 @ X22 ) @ X21 )
        = ( k6_subset_1 @ ( k8_relat_1 @ X20 @ X21 ) @ ( k8_relat_1 @ X22 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t136_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k8_relat_1 @ ( k4_xboole_0 @ X20 @ X22 ) @ X21 )
        = ( k4_xboole_0 @ ( k8_relat_1 @ X20 @ X21 ) @ ( k8_relat_1 @ X22 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t137_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k8_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t137_relat_1])).

thf('11',plain,(
    ( k8_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    $false ),
    inference(simplify,[status(thm)],['17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TuNciIoC9f
% 0.15/0.37  % Computer   : n019.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 14:34:08 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 32 iterations in 0.019s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.23/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.23/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(t136_relat_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ C ) =>
% 0.23/0.50       ( ( k8_relat_1 @ ( k6_subset_1 @ A @ B ) @ C ) =
% 0.23/0.50         ( k6_subset_1 @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ))).
% 0.23/0.50  thf('0', plain,
% 0.23/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.50         (((k8_relat_1 @ (k6_subset_1 @ X20 @ X22) @ X21)
% 0.23/0.50            = (k6_subset_1 @ (k8_relat_1 @ X20 @ X21) @ 
% 0.23/0.50               (k8_relat_1 @ X22 @ X21)))
% 0.23/0.50          | ~ (v1_relat_1 @ X21))),
% 0.23/0.50      inference('cnf', [status(esa)], [t136_relat_1])).
% 0.23/0.50  thf(redefinition_k6_subset_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (![X16 : $i, X17 : $i]:
% 0.23/0.50         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.23/0.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      (![X16 : $i, X17 : $i]:
% 0.23/0.50         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.23/0.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.50         (((k8_relat_1 @ (k4_xboole_0 @ X20 @ X22) @ X21)
% 0.23/0.50            = (k4_xboole_0 @ (k8_relat_1 @ X20 @ X21) @ 
% 0.23/0.50               (k8_relat_1 @ X22 @ X21)))
% 0.23/0.50          | ~ (v1_relat_1 @ X21))),
% 0.23/0.50      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.23/0.50  thf(t92_xboole_1, axiom,
% 0.23/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.23/0.50  thf('4', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.23/0.50  thf(idempotence_k3_xboole_0, axiom,
% 0.23/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.23/0.50  thf('5', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.23/0.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.23/0.50  thf(t100_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      (![X1 : $i, X2 : $i]:
% 0.23/0.50         ((k4_xboole_0 @ X1 @ X2)
% 0.23/0.50           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.23/0.50  thf('7', plain,
% 0.23/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.23/0.50      inference('sup+', [status(thm)], ['5', '6'])).
% 0.23/0.50  thf('8', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 0.23/0.50      inference('demod', [status(thm)], ['4', '7'])).
% 0.23/0.50  thf('9', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (((k8_relat_1 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (k1_xboole_0))
% 0.23/0.50          | ~ (v1_relat_1 @ X0))),
% 0.23/0.50      inference('sup+', [status(thm)], ['3', '8'])).
% 0.23/0.50  thf('10', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.23/0.50  thf(t137_relat_1, conjecture,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ A ) =>
% 0.23/0.50       ( ( k8_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i]:
% 0.23/0.50        ( ( v1_relat_1 @ A ) =>
% 0.23/0.50          ( ( k8_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t137_relat_1])).
% 0.23/0.50  thf('11', plain, (((k8_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((k8_relat_1 @ (k5_xboole_0 @ X0 @ X0) @ sk_A) != (k1_xboole_0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.23/0.50      inference('sup+', [status(thm)], ['5', '6'])).
% 0.23/0.50  thf('14', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((k8_relat_1 @ (k4_xboole_0 @ X0 @ X0) @ sk_A) != (k1_xboole_0))),
% 0.23/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.23/0.50  thf('15', plain,
% 0.23/0.50      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['9', '14'])).
% 0.23/0.50  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('17', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.23/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.23/0.50  thf('18', plain, ($false), inference('simplify', [status(thm)], ['17'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
