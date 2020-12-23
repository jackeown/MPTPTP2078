%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EpxX3DZFXy

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  57 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  216 ( 296 expanded)
%              Number of equality atoms :   29 (  41 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(rc1_relat_1,axiom,(
    ? [A: $i] :
      ( ( v1_relat_1 @ A )
      & ~ ( v1_xboole_0 @ A ) ) )).

thf('0',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_relat_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('5',plain,(
    ! [X11: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ X2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','8'])).

thf(t41_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) )
            = ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k4_relat_1 @ ( k6_subset_1 @ X15 @ X14 ) )
        = ( k6_subset_1 @ ( k4_relat_1 @ X15 ) @ ( k4_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t41_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k4_relat_1 @ ( k4_xboole_0 @ X15 @ X14 ) )
        = ( k4_xboole_0 @ ( k4_relat_1 @ X15 ) @ ( k4_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t66_relat_1,conjecture,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k4_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t66_relat_1])).

thf('17',plain,(
    ( k4_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( v1_relat_1 @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['15','20'])).

thf('22',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EpxX3DZFXy
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:27:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 25 iterations in 0.015s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.48  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.22/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(rc1_relat_1, axiom,
% 0.22/0.48    (?[A:$i]: ( ( v1_relat_1 @ A ) & ( ~( v1_xboole_0 @ A ) ) ))).
% 0.22/0.48  thf('0', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [rc1_relat_1])).
% 0.22/0.48  thf(t92_xboole_1, axiom,
% 0.22/0.48    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.48  thf('1', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ X2) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.48  thf(t69_enumset1, axiom,
% 0.22/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.48  thf('2', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.48  thf(t12_setfam_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X12 : $i, X13 : $i]:
% 0.22/0.48         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 0.22/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf(t11_setfam_1, axiom,
% 0.22/0.48    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.22/0.48  thf('5', plain, (![X11 : $i]: ((k1_setfam_1 @ (k1_tarski @ X11)) = (X11))),
% 0.22/0.48      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.22/0.48  thf('6', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.22/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf(t100_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.48           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf('9', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ X2) = (k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['1', '8'])).
% 0.22/0.48  thf(t41_relat_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( v1_relat_1 @ B ) =>
% 0.22/0.48           ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) ) =
% 0.22/0.48             ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) ))).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X14 : $i, X15 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X14)
% 0.22/0.48          | ((k4_relat_1 @ (k6_subset_1 @ X15 @ X14))
% 0.22/0.48              = (k6_subset_1 @ (k4_relat_1 @ X15) @ (k4_relat_1 @ X14)))
% 0.22/0.48          | ~ (v1_relat_1 @ X15))),
% 0.22/0.48      inference('cnf', [status(esa)], [t41_relat_1])).
% 0.22/0.48  thf(redefinition_k6_subset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X9 : $i, X10 : $i]:
% 0.22/0.48         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.22/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X9 : $i, X10 : $i]:
% 0.22/0.48         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.22/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X14 : $i, X15 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X14)
% 0.22/0.48          | ((k4_relat_1 @ (k4_xboole_0 @ X15 @ X14))
% 0.22/0.48              = (k4_xboole_0 @ (k4_relat_1 @ X15) @ (k4_relat_1 @ X14)))
% 0.22/0.48          | ~ (v1_relat_1 @ X15))),
% 0.22/0.48      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))
% 0.22/0.48          | ~ (v1_relat_1 @ X0)
% 0.22/0.48          | ~ (v1_relat_1 @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['9', '13'])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X0)
% 0.22/0.48          | ((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.48  thf('16', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ X2) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.48  thf(t66_relat_1, conjecture,
% 0.22/0.48    (( k4_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (( k4_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t66_relat_1])).
% 0.22/0.48  thf('17', plain, (((k4_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (![X0 : $i]: ((k4_relat_1 @ (k5_xboole_0 @ X0 @ X0)) != (k1_xboole_0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (![X0 : $i]: ((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) != (k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.48  thf('21', plain, (![X0 : $i]: ~ (v1_relat_1 @ X0)),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['15', '20'])).
% 0.22/0.48  thf('22', plain, ($false), inference('sup-', [status(thm)], ['0', '21'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
