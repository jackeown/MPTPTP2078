%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iy6rxgcWTD

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:31 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   60 (  70 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  415 ( 541 expanded)
%              Number of equality atoms :   31 (  40 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k10_relat_1 @ X14 @ X15 )
        = ( k10_relat_1 @ X14 @ ( k3_xboole_0 @ ( k2_relat_1 @ X14 ) @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X23 ) @ ( k6_relat_1 @ X22 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k9_relat_1 @ X12 @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X9 @ X10 ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('13',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k2_relat_1 @ X21 ) )
      | ( ( k9_relat_1 @ X21 @ ( k10_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X11: $i] :
      ( ( ( k9_relat_1 @ X11 @ ( k1_relat_1 @ X11 ) )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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

thf('20',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
     != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
     != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','29','30','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iy6rxgcWTD
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:23:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 339 iterations in 0.108s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.57  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.37/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.37/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.57  thf(t168_relat_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ B ) =>
% 0.37/0.57       ( ( k10_relat_1 @ B @ A ) =
% 0.37/0.57         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      (![X14 : $i, X15 : $i]:
% 0.37/0.57         (((k10_relat_1 @ X14 @ X15)
% 0.37/0.57            = (k10_relat_1 @ X14 @ (k3_xboole_0 @ (k2_relat_1 @ X14) @ X15)))
% 0.37/0.57          | ~ (v1_relat_1 @ X14))),
% 0.37/0.57      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.37/0.57  thf(t43_funct_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.37/0.57       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      (![X22 : $i, X23 : $i]:
% 0.37/0.57         ((k5_relat_1 @ (k6_relat_1 @ X23) @ (k6_relat_1 @ X22))
% 0.37/0.57           = (k6_relat_1 @ (k3_xboole_0 @ X22 @ X23)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.37/0.57  thf(t160_relat_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( v1_relat_1 @ B ) =>
% 0.37/0.57           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.37/0.57             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (![X12 : $i, X13 : $i]:
% 0.37/0.57         (~ (v1_relat_1 @ X12)
% 0.37/0.57          | ((k2_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.37/0.57              = (k9_relat_1 @ X12 @ (k2_relat_1 @ X13)))
% 0.37/0.57          | ~ (v1_relat_1 @ X13))),
% 0.37/0.57      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.37/0.57  thf(t71_relat_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.37/0.57       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.37/0.57  thf('3', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.37/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.37/0.57  thf(t144_relat_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ B ) =>
% 0.37/0.57       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         ((r1_tarski @ (k9_relat_1 @ X9 @ X10) @ (k2_relat_1 @ X9))
% 0.37/0.57          | ~ (v1_relat_1 @ X9))),
% 0.37/0.57      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.37/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.57  thf(fc3_funct_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.37/0.57       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.37/0.57  thf('6', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.37/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.37/0.57      inference('demod', [status(thm)], ['5', '6'])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.37/0.57           X0)
% 0.37/0.57          | ~ (v1_relat_1 @ X1)
% 0.37/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['2', '7'])).
% 0.37/0.57  thf('9', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.37/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.37/0.57           X0)
% 0.37/0.57          | ~ (v1_relat_1 @ X1))),
% 0.37/0.57      inference('demod', [status(thm)], ['8', '9'])).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 0.37/0.57           X1)
% 0.37/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['1', '10'])).
% 0.37/0.57  thf('12', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.37/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.37/0.57  thf('13', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.37/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.37/0.57      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.37/0.57  thf(t147_funct_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.57       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.37/0.57         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X20 : $i, X21 : $i]:
% 0.37/0.57         (~ (r1_tarski @ X20 @ (k2_relat_1 @ X21))
% 0.37/0.57          | ((k9_relat_1 @ X21 @ (k10_relat_1 @ X21 @ X20)) = (X20))
% 0.37/0.57          | ~ (v1_funct_1 @ X21)
% 0.37/0.57          | ~ (v1_relat_1 @ X21))),
% 0.37/0.57      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (v1_relat_1 @ X0)
% 0.37/0.57          | ~ (v1_funct_1 @ X0)
% 0.37/0.57          | ((k9_relat_1 @ X0 @ 
% 0.37/0.57              (k10_relat_1 @ X0 @ (k3_xboole_0 @ (k2_relat_1 @ X0) @ X1)))
% 0.37/0.57              = (k3_xboole_0 @ (k2_relat_1 @ X0) @ X1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 0.37/0.57            = (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0))
% 0.37/0.57          | ~ (v1_relat_1 @ X1)
% 0.37/0.57          | ~ (v1_funct_1 @ X1)
% 0.37/0.57          | ~ (v1_relat_1 @ X1))),
% 0.37/0.57      inference('sup+', [status(thm)], ['0', '16'])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (v1_funct_1 @ X1)
% 0.37/0.57          | ~ (v1_relat_1 @ X1)
% 0.37/0.57          | ((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 0.37/0.57              = (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.37/0.57  thf(t146_relat_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ A ) =>
% 0.37/0.57       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (![X11 : $i]:
% 0.37/0.57         (((k9_relat_1 @ X11 @ (k1_relat_1 @ X11)) = (k2_relat_1 @ X11))
% 0.37/0.57          | ~ (v1_relat_1 @ X11))),
% 0.37/0.57      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.37/0.57  thf(t148_funct_1, conjecture,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.57       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.37/0.57         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i,B:$i]:
% 0.37/0.57        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.57          ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.37/0.57            ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t148_funct_1])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.37/0.57         != (k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      ((((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.37/0.57          != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.37/0.57        | ~ (v1_relat_1 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.57  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.37/0.57         != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.37/0.57      inference('demod', [status(thm)], ['21', '22'])).
% 0.37/0.57  thf('24', plain,
% 0.37/0.57      ((((k3_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)
% 0.37/0.57          != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.37/0.57        | ~ (v1_relat_1 @ sk_B)
% 0.37/0.57        | ~ (v1_funct_1 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['18', '23'])).
% 0.37/0.57  thf(commutativity_k2_tarski, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.57  thf(t12_setfam_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      (![X7 : $i, X8 : $i]:
% 0.37/0.57         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.37/0.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('sup+', [status(thm)], ['25', '26'])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      (![X7 : $i, X8 : $i]:
% 0.37/0.57         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.37/0.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('sup+', [status(thm)], ['27', '28'])).
% 0.37/0.57  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('31', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B))
% 0.37/0.57         != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.37/0.57      inference('demod', [status(thm)], ['24', '29', '30', '31'])).
% 0.37/0.57  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
