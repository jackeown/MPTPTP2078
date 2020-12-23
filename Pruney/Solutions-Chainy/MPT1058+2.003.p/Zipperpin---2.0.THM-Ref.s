%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E0lx2y2Xa2

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:37 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   49 (  57 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :  289 ( 390 expanded)
%              Number of equality atoms :   32 (  40 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k6_subset_1 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ ( k6_subset_1 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('12',plain,(
    ! [X16: $i] :
      ( ( k6_subset_1 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C_1 )
    = ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C_1 )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('20',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X50 @ X49 ) @ X51 )
        = ( k3_xboole_0 @ X49 @ ( k10_relat_1 @ X50 @ X51 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('21',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C_1 )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E0lx2y2Xa2
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 473 iterations in 0.181s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.64  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.45/0.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.64  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(t175_funct_2, conjecture,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.64       ( ![B:$i,C:$i]:
% 0.45/0.64         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.45/0.64           ( ( k10_relat_1 @ A @ C ) =
% 0.45/0.64             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i]:
% 0.45/0.64        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.64          ( ![B:$i,C:$i]:
% 0.45/0.64            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.45/0.64              ( ( k10_relat_1 @ A @ C ) =
% 0.45/0.64                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.45/0.64  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(l32_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      (![X7 : $i, X9 : $i]:
% 0.45/0.64         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.45/0.64      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.45/0.64  thf(redefinition_k6_subset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      (![X24 : $i, X25 : $i]:
% 0.45/0.64         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (![X7 : $i, X9 : $i]:
% 0.45/0.64         (((k6_subset_1 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.45/0.64      inference('demod', [status(thm)], ['1', '2'])).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (((k6_subset_1 @ (k10_relat_1 @ sk_A @ sk_C_1) @ sk_B) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['0', '3'])).
% 0.45/0.64  thf(t48_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.45/0.64           = (k3_xboole_0 @ X18 @ X19))),
% 0.45/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      (![X24 : $i, X25 : $i]:
% 0.45/0.64         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X24 : $i, X25 : $i]:
% 0.45/0.64         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i]:
% 0.45/0.64         ((k6_subset_1 @ X18 @ (k6_subset_1 @ X18 @ X19))
% 0.45/0.64           = (k3_xboole_0 @ X18 @ X19))),
% 0.45/0.64      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (((k6_subset_1 @ (k10_relat_1 @ sk_A @ sk_C_1) @ k1_xboole_0)
% 0.45/0.64         = (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C_1) @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['4', '8'])).
% 0.45/0.64  thf(t3_boole, axiom,
% 0.45/0.64    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.64  thf('10', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.45/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X24 : $i, X25 : $i]:
% 0.45/0.64         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.64  thf('12', plain, (![X16 : $i]: ((k6_subset_1 @ X16 @ k1_xboole_0) = (X16))),
% 0.45/0.64      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.45/0.64         = (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C_1) @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['9', '12'])).
% 0.45/0.64  thf(commutativity_k2_tarski, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      (![X20 : $i, X21 : $i]:
% 0.45/0.64         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 0.45/0.64      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.45/0.64  thf(t12_setfam_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      (![X26 : $i, X27 : $i]:
% 0.45/0.64         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.45/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('sup+', [status(thm)], ['14', '15'])).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (![X26 : $i, X27 : $i]:
% 0.45/0.64         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.45/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.45/0.64         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.45/0.64      inference('demod', [status(thm)], ['13', '18'])).
% 0.45/0.64  thf(t139_funct_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ C ) =>
% 0.45/0.64       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.45/0.64         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.45/0.64         (((k10_relat_1 @ (k7_relat_1 @ X50 @ X49) @ X51)
% 0.45/0.64            = (k3_xboole_0 @ X49 @ (k10_relat_1 @ X50 @ X51)))
% 0.45/0.64          | ~ (v1_relat_1 @ X50))),
% 0.45/0.64      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.45/0.64         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C_1))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      ((((k10_relat_1 @ sk_A @ sk_C_1)
% 0.45/0.64          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))
% 0.45/0.64        | ~ (v1_relat_1 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.64  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.45/0.64         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.45/0.64      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.64  thf('25', plain, ($false),
% 0.45/0.64      inference('simplify_reflect-', [status(thm)], ['19', '24'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
