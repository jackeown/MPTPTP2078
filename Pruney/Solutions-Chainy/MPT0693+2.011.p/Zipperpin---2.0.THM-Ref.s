%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YlX9SdmHQN

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  60 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  361 ( 489 expanded)
%              Number of equality atoms :   30 (  40 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k10_relat_1 @ X18 @ X19 )
        = ( k10_relat_1 @ X18 @ ( k3_xboole_0 @ ( k2_relat_1 @ X18 ) @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k10_relat_1 @ X18 @ X19 )
        = ( k10_relat_1 @ X18 @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X18 ) @ X19 ) ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k2_relat_1 @ X21 ) )
      | ( ( k9_relat_1 @ X21 @ ( k10_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X17: $i] :
      ( ( ( k9_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t148_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_funct_1])).

thf('13',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
     != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ) )
     != ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
 != ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','23','24','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YlX9SdmHQN
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:26:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 130 iterations in 0.063s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(t168_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( k10_relat_1 @ B @ A ) =
% 0.21/0.52         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i]:
% 0.21/0.52         (((k10_relat_1 @ X18 @ X19)
% 0.21/0.52            = (k10_relat_1 @ X18 @ (k3_xboole_0 @ (k2_relat_1 @ X18) @ X19)))
% 0.21/0.52          | ~ (v1_relat_1 @ X18))),
% 0.21/0.52      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.21/0.52  thf(t12_setfam_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i]:
% 0.21/0.52         (((k10_relat_1 @ X18 @ X19)
% 0.21/0.52            = (k10_relat_1 @ X18 @ 
% 0.21/0.52               (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X18) @ X19))))
% 0.21/0.52          | ~ (v1_relat_1 @ X18))),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf(t48_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.21/0.52           = (k3_xboole_0 @ X4 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.21/0.52           = (k1_setfam_1 @ (k2_tarski @ X4 @ X5)))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf(t36_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.21/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X1)),
% 0.21/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf(t147_funct_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.52       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.52         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X20 @ (k2_relat_1 @ X21))
% 0.21/0.52          | ((k9_relat_1 @ X21 @ (k10_relat_1 @ X21 @ X20)) = (X20))
% 0.21/0.52          | ~ (v1_funct_1 @ X21)
% 0.21/0.52          | ~ (v1_relat_1 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | ((k9_relat_1 @ X0 @ 
% 0.21/0.52              (k10_relat_1 @ X0 @ 
% 0.21/0.52               (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X0) @ X1))))
% 0.21/0.52              = (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X0) @ X1))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 0.21/0.52            = (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X1) @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_funct_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['2', '9'])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (v1_funct_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 0.21/0.52              = (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X1) @ X0))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.52  thf(t146_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X17 : $i]:
% 0.21/0.52         (((k9_relat_1 @ X17 @ (k1_relat_1 @ X17)) = (k2_relat_1 @ X17))
% 0.21/0.52          | ~ (v1_relat_1 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.52  thf(t148_funct_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.52       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.21/0.52         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i]:
% 0.21/0.52        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.52          ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.21/0.52            ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t148_funct_1])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.21/0.52         != (k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      ((((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.21/0.52          != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.21/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.21/0.52         != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.21/0.52         != (k1_setfam_1 @ (k2_tarski @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.21/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      ((((k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ sk_B) @ sk_A))
% 0.21/0.52          != (k1_setfam_1 @ (k2_tarski @ sk_A @ (k2_relat_1 @ sk_B))))
% 0.21/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.52        | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '18'])).
% 0.21/0.52  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.21/0.52           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.52  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('25', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (((k1_setfam_1 @ (k2_tarski @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.21/0.52         != (k1_setfam_1 @ (k2_tarski @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.21/0.52      inference('demod', [status(thm)], ['19', '23', '24', '25'])).
% 0.21/0.52  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
