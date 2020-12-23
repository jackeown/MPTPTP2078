%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7OVQ9mB9Pe

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:39 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   49 (  54 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  305 ( 369 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t129_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
            = ( k8_relat_1 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t129_relat_1])).

thf('6',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X19 @ X18 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ( ( k8_relat_1 @ X21 @ X20 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ( k8_relat_1 @ sk_A @ sk_C )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7OVQ9mB9Pe
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:34:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 440 iterations in 0.200s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.66  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.45/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.66  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(commutativity_k2_tarski, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      (![X12 : $i, X13 : $i]:
% 0.45/0.66         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 0.45/0.66      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.45/0.66  thf(t12_setfam_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.66  thf('1', plain,
% 0.45/0.66      (![X14 : $i, X15 : $i]:
% 0.45/0.66         ((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (k3_xboole_0 @ X14 @ X15))),
% 0.45/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.66      inference('sup+', [status(thm)], ['0', '1'])).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      (![X14 : $i, X15 : $i]:
% 0.45/0.66         ((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (k3_xboole_0 @ X14 @ X15))),
% 0.45/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.66  thf('4', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.66      inference('sup+', [status(thm)], ['2', '3'])).
% 0.45/0.66  thf(t48_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X10 : $i, X11 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.45/0.66           = (k3_xboole_0 @ X10 @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.66  thf(t129_relat_1, conjecture,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ C ) =>
% 0.45/0.66       ( ( r1_tarski @ A @ B ) =>
% 0.45/0.66         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.66        ( ( v1_relat_1 @ C ) =>
% 0.45/0.66          ( ( r1_tarski @ A @ B ) =>
% 0.45/0.66            ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) =
% 0.45/0.66              ( k8_relat_1 @ A @ C ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t129_relat_1])).
% 0.45/0.66  thf('6', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t36_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.45/0.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.45/0.66  thf(t12_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      (![X6 : $i, X7 : $i]:
% 0.45/0.66         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.45/0.66  thf('9', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.66  thf(t11_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.66         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.45/0.66      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.45/0.66      inference('sup-', [status(thm)], ['6', '11'])).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.45/0.66      inference('sup+', [status(thm)], ['5', '12'])).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B)),
% 0.45/0.66      inference('sup+', [status(thm)], ['4', '13'])).
% 0.45/0.66  thf(t119_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ B ) =>
% 0.45/0.66       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.45/0.66         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      (![X18 : $i, X19 : $i]:
% 0.45/0.66         (((k2_relat_1 @ (k8_relat_1 @ X19 @ X18))
% 0.45/0.66            = (k3_xboole_0 @ (k2_relat_1 @ X18) @ X19))
% 0.45/0.66          | ~ (v1_relat_1 @ X18))),
% 0.45/0.66      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.45/0.66  thf(t125_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ B ) =>
% 0.45/0.66       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.45/0.66         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      (![X20 : $i, X21 : $i]:
% 0.45/0.66         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.45/0.66          | ((k8_relat_1 @ X21 @ X20) = (X20))
% 0.45/0.66          | ~ (v1_relat_1 @ X20))),
% 0.45/0.66      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (~ (r1_tarski @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ X2)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1))
% 0.45/0.66          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X0 @ X1))
% 0.45/0.66              = (k8_relat_1 @ X0 @ X1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.45/0.66            = (k8_relat_1 @ sk_A @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['14', '17'])).
% 0.45/0.66  thf(dt_k8_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      (![X16 : $i, X17 : $i]:
% 0.45/0.66         ((v1_relat_1 @ (k8_relat_1 @ X16 @ X17)) | ~ (v1_relat_1 @ X17))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.45/0.66              = (k8_relat_1 @ sk_A @ X0)))),
% 0.45/0.66      inference('clc', [status(thm)], ['18', '19'])).
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.45/0.66         != (k8_relat_1 @ sk_A @ sk_C))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      ((((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.66  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      (((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.66  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
