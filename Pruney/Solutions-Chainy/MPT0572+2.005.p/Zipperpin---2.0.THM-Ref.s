%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MmbslzOmVx

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:15 EST 2020

% Result     : Theorem 5.18s
% Output     : Refutation 5.18s
% Verified   : 
% Statistics : Number of formulae       :   46 (  55 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  331 ( 424 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6
        = ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k10_relat_1 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X18 @ X19 ) @ ( k10_relat_1 @ X18 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6
        = ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k10_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t176_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t176_relat_1])).

thf('22',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MmbslzOmVx
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:21:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.18/5.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.18/5.41  % Solved by: fo/fo7.sh
% 5.18/5.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.18/5.41  % done 3799 iterations in 4.979s
% 5.18/5.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.18/5.41  % SZS output start Refutation
% 5.18/5.41  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.18/5.41  thf(sk_B_type, type, sk_B: $i).
% 5.18/5.41  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.18/5.41  thf(sk_A_type, type, sk_A: $i).
% 5.18/5.41  thf(sk_C_type, type, sk_C: $i).
% 5.18/5.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.18/5.41  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 5.18/5.41  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 5.18/5.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.18/5.41  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.18/5.41  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.18/5.41  thf(commutativity_k2_tarski, axiom,
% 5.18/5.41    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 5.18/5.41  thf('0', plain,
% 5.18/5.41      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 5.18/5.41      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.18/5.41  thf(t12_setfam_1, axiom,
% 5.18/5.41    (![A:$i,B:$i]:
% 5.18/5.41     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.18/5.41  thf('1', plain,
% 5.18/5.41      (![X16 : $i, X17 : $i]:
% 5.18/5.41         ((k1_setfam_1 @ (k2_tarski @ X16 @ X17)) = (k3_xboole_0 @ X16 @ X17))),
% 5.18/5.41      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.18/5.41  thf('2', plain,
% 5.18/5.41      (![X0 : $i, X1 : $i]:
% 5.18/5.41         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 5.18/5.41      inference('sup+', [status(thm)], ['0', '1'])).
% 5.18/5.41  thf('3', plain,
% 5.18/5.41      (![X16 : $i, X17 : $i]:
% 5.18/5.41         ((k1_setfam_1 @ (k2_tarski @ X16 @ X17)) = (k3_xboole_0 @ X16 @ X17))),
% 5.18/5.41      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.18/5.41  thf('4', plain,
% 5.18/5.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.18/5.41      inference('sup+', [status(thm)], ['2', '3'])).
% 5.18/5.41  thf(t17_xboole_1, axiom,
% 5.18/5.41    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 5.18/5.41  thf('5', plain,
% 5.18/5.41      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 5.18/5.41      inference('cnf', [status(esa)], [t17_xboole_1])).
% 5.18/5.41  thf('6', plain,
% 5.18/5.41      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 5.18/5.41      inference('sup+', [status(thm)], ['4', '5'])).
% 5.18/5.41  thf(t45_xboole_1, axiom,
% 5.18/5.41    (![A:$i,B:$i]:
% 5.18/5.41     ( ( r1_tarski @ A @ B ) =>
% 5.18/5.41       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 5.18/5.41  thf('7', plain,
% 5.18/5.41      (![X5 : $i, X6 : $i]:
% 5.18/5.41         (((X6) = (k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5)))
% 5.18/5.41          | ~ (r1_tarski @ X5 @ X6))),
% 5.18/5.41      inference('cnf', [status(esa)], [t45_xboole_1])).
% 5.18/5.41  thf('8', plain,
% 5.18/5.41      (![X0 : $i, X1 : $i]:
% 5.18/5.41         ((X0)
% 5.18/5.41           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 5.18/5.41              (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 5.18/5.41      inference('sup-', [status(thm)], ['6', '7'])).
% 5.18/5.41  thf(t175_relat_1, axiom,
% 5.18/5.41    (![A:$i,B:$i,C:$i]:
% 5.18/5.41     ( ( v1_relat_1 @ C ) =>
% 5.18/5.41       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 5.18/5.41         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 5.18/5.41  thf('9', plain,
% 5.18/5.41      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.18/5.41         (((k10_relat_1 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 5.18/5.41            = (k2_xboole_0 @ (k10_relat_1 @ X18 @ X19) @ 
% 5.18/5.41               (k10_relat_1 @ X18 @ X20)))
% 5.18/5.41          | ~ (v1_relat_1 @ X18))),
% 5.18/5.41      inference('cnf', [status(esa)], [t175_relat_1])).
% 5.18/5.41  thf(t7_xboole_1, axiom,
% 5.18/5.41    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 5.18/5.41  thf('10', plain,
% 5.18/5.41      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 5.18/5.41      inference('cnf', [status(esa)], [t7_xboole_1])).
% 5.18/5.41  thf('11', plain,
% 5.18/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.18/5.41         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 5.18/5.41           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 5.18/5.41          | ~ (v1_relat_1 @ X2))),
% 5.18/5.41      inference('sup+', [status(thm)], ['9', '10'])).
% 5.18/5.41  thf('12', plain,
% 5.18/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.18/5.41         ((r1_tarski @ (k10_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 5.18/5.41           (k10_relat_1 @ X2 @ X0))
% 5.18/5.41          | ~ (v1_relat_1 @ X2))),
% 5.18/5.41      inference('sup+', [status(thm)], ['8', '11'])).
% 5.18/5.41  thf('13', plain,
% 5.18/5.41      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 5.18/5.41      inference('cnf', [status(esa)], [t17_xboole_1])).
% 5.18/5.41  thf('14', plain,
% 5.18/5.41      (![X5 : $i, X6 : $i]:
% 5.18/5.41         (((X6) = (k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5)))
% 5.18/5.41          | ~ (r1_tarski @ X5 @ X6))),
% 5.18/5.41      inference('cnf', [status(esa)], [t45_xboole_1])).
% 5.18/5.41  thf('15', plain,
% 5.18/5.41      (![X0 : $i, X1 : $i]:
% 5.18/5.41         ((X0)
% 5.18/5.41           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 5.18/5.41              (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))))),
% 5.18/5.41      inference('sup-', [status(thm)], ['13', '14'])).
% 5.18/5.41  thf('16', plain,
% 5.18/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.18/5.41         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 5.18/5.41           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 5.18/5.41          | ~ (v1_relat_1 @ X2))),
% 5.18/5.41      inference('sup+', [status(thm)], ['9', '10'])).
% 5.18/5.41  thf('17', plain,
% 5.18/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.18/5.41         ((r1_tarski @ (k10_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 5.18/5.41           (k10_relat_1 @ X2 @ X0))
% 5.18/5.41          | ~ (v1_relat_1 @ X2))),
% 5.18/5.41      inference('sup+', [status(thm)], ['15', '16'])).
% 5.18/5.41  thf(t19_xboole_1, axiom,
% 5.18/5.41    (![A:$i,B:$i,C:$i]:
% 5.18/5.41     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 5.18/5.41       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 5.18/5.41  thf('18', plain,
% 5.18/5.41      (![X2 : $i, X3 : $i, X4 : $i]:
% 5.18/5.41         (~ (r1_tarski @ X2 @ X3)
% 5.18/5.41          | ~ (r1_tarski @ X2 @ X4)
% 5.18/5.41          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 5.18/5.41      inference('cnf', [status(esa)], [t19_xboole_1])).
% 5.18/5.41  thf('19', plain,
% 5.18/5.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.18/5.41         (~ (v1_relat_1 @ X1)
% 5.18/5.41          | (r1_tarski @ (k10_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 5.18/5.41             (k3_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X3))
% 5.18/5.41          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 5.18/5.41      inference('sup-', [status(thm)], ['17', '18'])).
% 5.18/5.41  thf('20', plain,
% 5.18/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.18/5.41         (~ (v1_relat_1 @ X1)
% 5.18/5.41          | (r1_tarski @ (k10_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 5.18/5.41             (k3_xboole_0 @ (k10_relat_1 @ X1 @ X2) @ (k10_relat_1 @ X1 @ X0)))
% 5.18/5.41          | ~ (v1_relat_1 @ X1))),
% 5.18/5.41      inference('sup-', [status(thm)], ['12', '19'])).
% 5.18/5.41  thf('21', plain,
% 5.18/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.18/5.41         ((r1_tarski @ (k10_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 5.18/5.41           (k3_xboole_0 @ (k10_relat_1 @ X1 @ X2) @ (k10_relat_1 @ X1 @ X0)))
% 5.18/5.41          | ~ (v1_relat_1 @ X1))),
% 5.18/5.41      inference('simplify', [status(thm)], ['20'])).
% 5.18/5.41  thf(t176_relat_1, conjecture,
% 5.18/5.41    (![A:$i,B:$i,C:$i]:
% 5.18/5.41     ( ( v1_relat_1 @ C ) =>
% 5.18/5.41       ( r1_tarski @
% 5.18/5.41         ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 5.18/5.41         ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 5.18/5.41  thf(zf_stmt_0, negated_conjecture,
% 5.18/5.41    (~( ![A:$i,B:$i,C:$i]:
% 5.18/5.41        ( ( v1_relat_1 @ C ) =>
% 5.18/5.41          ( r1_tarski @
% 5.18/5.41            ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 5.18/5.41            ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 5.18/5.41    inference('cnf.neg', [status(esa)], [t176_relat_1])).
% 5.18/5.41  thf('22', plain,
% 5.18/5.41      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 5.18/5.41          (k3_xboole_0 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 5.18/5.41           (k10_relat_1 @ sk_C @ sk_B)))),
% 5.18/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.41  thf('23', plain, (~ (v1_relat_1 @ sk_C)),
% 5.18/5.41      inference('sup-', [status(thm)], ['21', '22'])).
% 5.18/5.41  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 5.18/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.41  thf('25', plain, ($false), inference('demod', [status(thm)], ['23', '24'])).
% 5.18/5.41  
% 5.18/5.41  % SZS output end Refutation
% 5.18/5.41  
% 5.18/5.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
