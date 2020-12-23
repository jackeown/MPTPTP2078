%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8x3wKKL5qu

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:37 EST 2020

% Result     : Theorem 3.36s
% Output     : Refutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   52 (  70 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  403 ( 562 expanded)
%              Number of equality atoms :   22 (  38 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) @ X23 )
        = ( k3_xboole_0 @ X21 @ ( k10_relat_1 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) @ X23 )
        = ( k3_xboole_0 @ X21 @ ( k10_relat_1 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k10_relat_1 @ X19 @ X20 )
        = ( k10_relat_1 @ X19 @ ( k3_xboole_0 @ ( k2_relat_1 @ X19 ) @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k3_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','22'])).

thf(t151_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t151_funct_1])).

thf('24',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('26',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8x3wKKL5qu
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.36/3.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.36/3.62  % Solved by: fo/fo7.sh
% 3.36/3.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.36/3.62  % done 1691 iterations in 3.140s
% 3.36/3.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.36/3.62  % SZS output start Refutation
% 3.36/3.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.36/3.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.36/3.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.36/3.62  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.36/3.62  thf(sk_C_type, type, sk_C: $i).
% 3.36/3.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.36/3.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 3.36/3.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.36/3.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.36/3.62  thf(sk_A_type, type, sk_A: $i).
% 3.36/3.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.36/3.62  thf(sk_B_type, type, sk_B: $i).
% 3.36/3.62  thf(commutativity_k2_tarski, axiom,
% 3.36/3.62    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 3.36/3.62  thf('0', plain,
% 3.36/3.62      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 3.36/3.62      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.36/3.62  thf(t12_setfam_1, axiom,
% 3.36/3.62    (![A:$i,B:$i]:
% 3.36/3.62     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.36/3.62  thf('1', plain,
% 3.36/3.62      (![X13 : $i, X14 : $i]:
% 3.36/3.62         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 3.36/3.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.36/3.62  thf('2', plain,
% 3.36/3.62      (![X0 : $i, X1 : $i]:
% 3.36/3.62         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 3.36/3.62      inference('sup+', [status(thm)], ['0', '1'])).
% 3.36/3.62  thf('3', plain,
% 3.36/3.62      (![X13 : $i, X14 : $i]:
% 3.36/3.62         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 3.36/3.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.36/3.62  thf('4', plain,
% 3.36/3.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.36/3.62      inference('sup+', [status(thm)], ['2', '3'])).
% 3.36/3.62  thf(t139_funct_1, axiom,
% 3.36/3.62    (![A:$i,B:$i,C:$i]:
% 3.36/3.62     ( ( v1_relat_1 @ C ) =>
% 3.36/3.62       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 3.36/3.62         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 3.36/3.62  thf('5', plain,
% 3.36/3.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.36/3.62         (((k10_relat_1 @ (k7_relat_1 @ X22 @ X21) @ X23)
% 3.36/3.62            = (k3_xboole_0 @ X21 @ (k10_relat_1 @ X22 @ X23)))
% 3.36/3.62          | ~ (v1_relat_1 @ X22))),
% 3.36/3.62      inference('cnf', [status(esa)], [t139_funct_1])).
% 3.36/3.62  thf('6', plain,
% 3.36/3.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.36/3.62         (((k10_relat_1 @ (k7_relat_1 @ X22 @ X21) @ X23)
% 3.36/3.62            = (k3_xboole_0 @ X21 @ (k10_relat_1 @ X22 @ X23)))
% 3.36/3.62          | ~ (v1_relat_1 @ X22))),
% 3.36/3.62      inference('cnf', [status(esa)], [t139_funct_1])).
% 3.36/3.62  thf(t148_relat_1, axiom,
% 3.36/3.62    (![A:$i,B:$i]:
% 3.36/3.62     ( ( v1_relat_1 @ B ) =>
% 3.36/3.62       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 3.36/3.62  thf('7', plain,
% 3.36/3.62      (![X17 : $i, X18 : $i]:
% 3.36/3.62         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 3.36/3.62          | ~ (v1_relat_1 @ X17))),
% 3.36/3.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.36/3.62  thf(t168_relat_1, axiom,
% 3.36/3.62    (![A:$i,B:$i]:
% 3.36/3.62     ( ( v1_relat_1 @ B ) =>
% 3.36/3.62       ( ( k10_relat_1 @ B @ A ) =
% 3.36/3.62         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 3.36/3.62  thf('8', plain,
% 3.36/3.62      (![X19 : $i, X20 : $i]:
% 3.36/3.62         (((k10_relat_1 @ X19 @ X20)
% 3.36/3.62            = (k10_relat_1 @ X19 @ (k3_xboole_0 @ (k2_relat_1 @ X19) @ X20)))
% 3.36/3.62          | ~ (v1_relat_1 @ X19))),
% 3.36/3.62      inference('cnf', [status(esa)], [t168_relat_1])).
% 3.36/3.62  thf('9', plain,
% 3.36/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.36/3.62         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.36/3.62            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 3.36/3.62               (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X2)))
% 3.36/3.62          | ~ (v1_relat_1 @ X1)
% 3.36/3.62          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 3.36/3.62      inference('sup+', [status(thm)], ['7', '8'])).
% 3.36/3.62  thf(dt_k7_relat_1, axiom,
% 3.36/3.62    (![A:$i,B:$i]:
% 3.36/3.62     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 3.36/3.62  thf('10', plain,
% 3.36/3.62      (![X15 : $i, X16 : $i]:
% 3.36/3.62         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k7_relat_1 @ X15 @ X16)))),
% 3.36/3.62      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 3.36/3.62  thf('11', plain,
% 3.36/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.36/3.62         (~ (v1_relat_1 @ X1)
% 3.36/3.62          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.36/3.62              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 3.36/3.62                 (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X2))))),
% 3.36/3.62      inference('clc', [status(thm)], ['9', '10'])).
% 3.36/3.62  thf('12', plain,
% 3.36/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.36/3.62         (((k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 3.36/3.62            = (k3_xboole_0 @ X1 @ 
% 3.36/3.62               (k10_relat_1 @ X2 @ (k3_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ X0))))
% 3.36/3.62          | ~ (v1_relat_1 @ X2)
% 3.36/3.62          | ~ (v1_relat_1 @ X2))),
% 3.36/3.62      inference('sup+', [status(thm)], ['6', '11'])).
% 3.36/3.62  thf('13', plain,
% 3.36/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.36/3.62         (~ (v1_relat_1 @ X2)
% 3.36/3.62          | ((k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 3.36/3.62              = (k3_xboole_0 @ X1 @ 
% 3.36/3.62                 (k10_relat_1 @ X2 @ 
% 3.36/3.62                  (k3_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ X0)))))),
% 3.36/3.62      inference('simplify', [status(thm)], ['12'])).
% 3.36/3.62  thf('14', plain,
% 3.36/3.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.36/3.62      inference('sup+', [status(thm)], ['2', '3'])).
% 3.36/3.62  thf(d10_xboole_0, axiom,
% 3.36/3.62    (![A:$i,B:$i]:
% 3.36/3.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.36/3.62  thf('15', plain,
% 3.36/3.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.36/3.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.36/3.62  thf('16', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.36/3.62      inference('simplify', [status(thm)], ['15'])).
% 3.36/3.62  thf(t108_xboole_1, axiom,
% 3.36/3.62    (![A:$i,B:$i,C:$i]:
% 3.36/3.62     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 3.36/3.62  thf('17', plain,
% 3.36/3.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.36/3.62         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k3_xboole_0 @ X3 @ X5) @ X4))),
% 3.36/3.62      inference('cnf', [status(esa)], [t108_xboole_1])).
% 3.36/3.62  thf('18', plain,
% 3.36/3.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 3.36/3.62      inference('sup-', [status(thm)], ['16', '17'])).
% 3.36/3.62  thf('19', plain,
% 3.36/3.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 3.36/3.62      inference('sup+', [status(thm)], ['14', '18'])).
% 3.36/3.62  thf('20', plain,
% 3.36/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.36/3.62         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 3.36/3.62           (k10_relat_1 @ X2 @ (k3_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ X0)))
% 3.36/3.62          | ~ (v1_relat_1 @ X2))),
% 3.36/3.62      inference('sup+', [status(thm)], ['13', '19'])).
% 3.36/3.62  thf('21', plain,
% 3.36/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.36/3.62         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 3.36/3.62           (k10_relat_1 @ X1 @ (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0)))
% 3.36/3.62          | ~ (v1_relat_1 @ X1)
% 3.36/3.62          | ~ (v1_relat_1 @ X1))),
% 3.36/3.62      inference('sup+', [status(thm)], ['5', '20'])).
% 3.36/3.62  thf('22', plain,
% 3.36/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.36/3.62         (~ (v1_relat_1 @ X1)
% 3.36/3.62          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 3.36/3.62             (k10_relat_1 @ X1 @ (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))))),
% 3.36/3.62      inference('simplify', [status(thm)], ['21'])).
% 3.36/3.62  thf('23', plain,
% 3.36/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.36/3.62         ((r1_tarski @ (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2)) @ 
% 3.36/3.62           (k10_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k9_relat_1 @ X1 @ X0))))
% 3.36/3.62          | ~ (v1_relat_1 @ X1))),
% 3.36/3.62      inference('sup+', [status(thm)], ['4', '22'])).
% 3.36/3.62  thf(t151_funct_1, conjecture,
% 3.36/3.62    (![A:$i,B:$i,C:$i]:
% 3.36/3.62     ( ( v1_relat_1 @ C ) =>
% 3.36/3.62       ( r1_tarski @
% 3.36/3.62         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) @ 
% 3.36/3.62         ( k10_relat_1 @ C @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ))).
% 3.36/3.62  thf(zf_stmt_0, negated_conjecture,
% 3.36/3.62    (~( ![A:$i,B:$i,C:$i]:
% 3.36/3.62        ( ( v1_relat_1 @ C ) =>
% 3.36/3.62          ( r1_tarski @
% 3.36/3.62            ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) @ 
% 3.36/3.62            ( k10_relat_1 @ C @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ) )),
% 3.36/3.62    inference('cnf.neg', [status(esa)], [t151_funct_1])).
% 3.36/3.62  thf('24', plain,
% 3.36/3.62      (~ (r1_tarski @ (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B)) @ 
% 3.36/3.62          (k10_relat_1 @ sk_C @ 
% 3.36/3.62           (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B)))),
% 3.36/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.62  thf('25', plain,
% 3.36/3.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.36/3.62      inference('sup+', [status(thm)], ['2', '3'])).
% 3.36/3.62  thf('26', plain,
% 3.36/3.62      (~ (r1_tarski @ (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B)) @ 
% 3.36/3.62          (k10_relat_1 @ sk_C @ 
% 3.36/3.62           (k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A))))),
% 3.36/3.62      inference('demod', [status(thm)], ['24', '25'])).
% 3.36/3.62  thf('27', plain, (~ (v1_relat_1 @ sk_C)),
% 3.36/3.62      inference('sup-', [status(thm)], ['23', '26'])).
% 3.36/3.62  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 3.36/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.62  thf('29', plain, ($false), inference('demod', [status(thm)], ['27', '28'])).
% 3.36/3.62  
% 3.36/3.62  % SZS output end Refutation
% 3.36/3.62  
% 3.36/3.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
