%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5MXTE1kDWn

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:33 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :   50 (  71 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  412 ( 619 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X18 @ ( k10_relat_1 @ X18 @ X19 ) ) @ X19 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf(t154_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X15 @ X16 ) @ ( k9_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t154_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ X3 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X15 @ X16 ) @ ( k9_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t154_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ ( k3_xboole_0 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','21'])).

thf(t149_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t149_funct_1])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) @ ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['26','27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5MXTE1kDWn
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:40:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 1.02/1.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.02/1.20  % Solved by: fo/fo7.sh
% 1.02/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.20  % done 499 iterations in 0.753s
% 1.02/1.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.02/1.20  % SZS output start Refutation
% 1.02/1.20  thf(sk_C_type, type, sk_C: $i).
% 1.02/1.20  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.02/1.20  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.02/1.20  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.02/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.02/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.02/1.20  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.02/1.20  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.02/1.20  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.02/1.20  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.02/1.20  thf(commutativity_k2_tarski, axiom,
% 1.02/1.20    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.02/1.20  thf('0', plain,
% 1.02/1.20      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 1.02/1.20      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.02/1.20  thf(t12_setfam_1, axiom,
% 1.02/1.20    (![A:$i,B:$i]:
% 1.02/1.20     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.02/1.20  thf('1', plain,
% 1.02/1.20      (![X13 : $i, X14 : $i]:
% 1.02/1.20         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 1.02/1.20      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.02/1.20  thf('2', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.02/1.20      inference('sup+', [status(thm)], ['0', '1'])).
% 1.02/1.20  thf('3', plain,
% 1.02/1.20      (![X13 : $i, X14 : $i]:
% 1.02/1.20         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 1.02/1.20      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.02/1.20  thf('4', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.02/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 1.02/1.20  thf(t145_funct_1, axiom,
% 1.02/1.20    (![A:$i,B:$i]:
% 1.02/1.20     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.02/1.20       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 1.02/1.20  thf('5', plain,
% 1.02/1.20      (![X18 : $i, X19 : $i]:
% 1.02/1.20         ((r1_tarski @ (k9_relat_1 @ X18 @ (k10_relat_1 @ X18 @ X19)) @ X19)
% 1.02/1.20          | ~ (v1_funct_1 @ X18)
% 1.02/1.20          | ~ (v1_relat_1 @ X18))),
% 1.02/1.20      inference('cnf', [status(esa)], [t145_funct_1])).
% 1.02/1.20  thf(t154_relat_1, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i]:
% 1.02/1.20     ( ( v1_relat_1 @ C ) =>
% 1.02/1.20       ( r1_tarski @
% 1.02/1.20         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.02/1.20         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 1.02/1.20  thf('6', plain,
% 1.02/1.20      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.02/1.20         ((r1_tarski @ (k9_relat_1 @ X15 @ (k3_xboole_0 @ X16 @ X17)) @ 
% 1.02/1.20           (k3_xboole_0 @ (k9_relat_1 @ X15 @ X16) @ (k9_relat_1 @ X15 @ X17)))
% 1.02/1.20          | ~ (v1_relat_1 @ X15))),
% 1.02/1.20      inference('cnf', [status(esa)], [t154_relat_1])).
% 1.02/1.20  thf('7', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.02/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 1.02/1.20  thf(t18_xboole_1, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i]:
% 1.02/1.20     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 1.02/1.20  thf('8', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.02/1.20      inference('cnf', [status(esa)], [t18_xboole_1])).
% 1.02/1.20  thf('9', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 1.02/1.20      inference('sup-', [status(thm)], ['7', '8'])).
% 1.02/1.20  thf('10', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X1)
% 1.02/1.20          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 1.02/1.20             (k9_relat_1 @ X1 @ X0)))),
% 1.02/1.20      inference('sup-', [status(thm)], ['6', '9'])).
% 1.02/1.20  thf(t1_xboole_1, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i]:
% 1.02/1.20     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.02/1.20       ( r1_tarski @ A @ C ) ))).
% 1.02/1.20  thf('11', plain,
% 1.02/1.20      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.02/1.20         (~ (r1_tarski @ X6 @ X7)
% 1.02/1.20          | ~ (r1_tarski @ X7 @ X8)
% 1.02/1.20          | (r1_tarski @ X6 @ X8))),
% 1.02/1.20      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.02/1.20  thf('12', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X1)
% 1.02/1.20          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ X3)
% 1.02/1.20          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X3))),
% 1.02/1.20      inference('sup-', [status(thm)], ['10', '11'])).
% 1.02/1.20  thf('13', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X1)
% 1.02/1.20          | ~ (v1_funct_1 @ X1)
% 1.02/1.20          | (r1_tarski @ 
% 1.02/1.20             (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 1.02/1.20             X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X1))),
% 1.02/1.20      inference('sup-', [status(thm)], ['5', '12'])).
% 1.02/1.20  thf('14', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         ((r1_tarski @ 
% 1.02/1.20           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 1.02/1.20           X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_relat_1 @ X1))),
% 1.02/1.20      inference('simplify', [status(thm)], ['13'])).
% 1.02/1.20  thf('15', plain,
% 1.02/1.20      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.02/1.20         ((r1_tarski @ (k9_relat_1 @ X15 @ (k3_xboole_0 @ X16 @ X17)) @ 
% 1.02/1.20           (k3_xboole_0 @ (k9_relat_1 @ X15 @ X16) @ (k9_relat_1 @ X15 @ X17)))
% 1.02/1.20          | ~ (v1_relat_1 @ X15))),
% 1.02/1.20      inference('cnf', [status(esa)], [t154_relat_1])).
% 1.02/1.20  thf('16', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.02/1.20      inference('cnf', [status(esa)], [t18_xboole_1])).
% 1.02/1.20  thf('17', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X1)
% 1.02/1.20          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 1.02/1.20             (k9_relat_1 @ X1 @ X2)))),
% 1.02/1.20      inference('sup-', [status(thm)], ['15', '16'])).
% 1.02/1.20  thf(t19_xboole_1, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i]:
% 1.02/1.20     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.02/1.20       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.02/1.20  thf('18', plain,
% 1.02/1.20      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.02/1.20         (~ (r1_tarski @ X3 @ X4)
% 1.02/1.20          | ~ (r1_tarski @ X3 @ X5)
% 1.02/1.20          | (r1_tarski @ X3 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.02/1.20      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.02/1.20  thf('19', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X1)
% 1.02/1.20          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 1.02/1.20             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 1.02/1.20          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 1.02/1.20      inference('sup-', [status(thm)], ['17', '18'])).
% 1.02/1.20  thf('20', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X1)
% 1.02/1.20          | ~ (v1_funct_1 @ X1)
% 1.02/1.20          | (r1_tarski @ 
% 1.02/1.20             (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 1.02/1.20             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))
% 1.02/1.20          | ~ (v1_relat_1 @ X1))),
% 1.02/1.20      inference('sup-', [status(thm)], ['14', '19'])).
% 1.02/1.20  thf('21', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         ((r1_tarski @ 
% 1.02/1.20           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 1.02/1.20           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))
% 1.02/1.20          | ~ (v1_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_relat_1 @ X1))),
% 1.02/1.20      inference('simplify', [status(thm)], ['20'])).
% 1.02/1.20  thf('22', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         ((r1_tarski @ 
% 1.02/1.20           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 1.02/1.20           (k3_xboole_0 @ X2 @ (k9_relat_1 @ X1 @ X0)))
% 1.02/1.20          | ~ (v1_relat_1 @ X1)
% 1.02/1.20          | ~ (v1_funct_1 @ X1))),
% 1.02/1.20      inference('sup+', [status(thm)], ['4', '21'])).
% 1.02/1.20  thf(t149_funct_1, conjecture,
% 1.02/1.20    (![A:$i,B:$i,C:$i]:
% 1.02/1.20     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.02/1.20       ( r1_tarski @
% 1.02/1.20         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 1.02/1.20         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ))).
% 1.02/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.20    (~( ![A:$i,B:$i,C:$i]:
% 1.02/1.20        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.02/1.20          ( r1_tarski @
% 1.02/1.20            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 1.02/1.20            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )),
% 1.02/1.20    inference('cnf.neg', [status(esa)], [t149_funct_1])).
% 1.02/1.20  thf('23', plain,
% 1.02/1.20      (~ (r1_tarski @ 
% 1.02/1.20          (k9_relat_1 @ sk_C @ 
% 1.02/1.20           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))) @ 
% 1.02/1.20          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('24', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.02/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 1.02/1.20  thf('25', plain,
% 1.02/1.20      (~ (r1_tarski @ 
% 1.02/1.20          (k9_relat_1 @ sk_C @ 
% 1.02/1.20           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))) @ 
% 1.02/1.20          (k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A)))),
% 1.02/1.20      inference('demod', [status(thm)], ['23', '24'])).
% 1.02/1.20  thf('26', plain, ((~ (v1_funct_1 @ sk_C) | ~ (v1_relat_1 @ sk_C))),
% 1.02/1.20      inference('sup-', [status(thm)], ['22', '25'])).
% 1.02/1.20  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('29', plain, ($false),
% 1.02/1.20      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.02/1.20  
% 1.02/1.20  % SZS output end Refutation
% 1.02/1.20  
% 1.02/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
