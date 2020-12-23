%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8gXG3oZImu

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   47 (  55 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :  294 ( 400 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( ( k7_relat_1 @ X20 @ X21 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B )
    = ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('8',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('10',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','9','10','15','16'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('18',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k3_xboole_0 @ X24 @ ( k10_relat_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('19',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8gXG3oZImu
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:41:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 57 iterations in 0.031s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.46  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.46  thf(t175_funct_2, conjecture,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.46       ( ![B:$i,C:$i]:
% 0.22/0.46         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.22/0.46           ( ( k10_relat_1 @ A @ C ) =
% 0.22/0.46             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i]:
% 0.22/0.46        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.46          ( ![B:$i,C:$i]:
% 0.22/0.46            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.22/0.46              ( ( k10_relat_1 @ A @ C ) =
% 0.22/0.46                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.22/0.46  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(t71_relat_1, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.46       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.46  thf('1', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.22/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.46  thf(t97_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ B ) =>
% 0.22/0.46       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.22/0.46         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.22/0.46  thf('2', plain,
% 0.22/0.46      (![X20 : $i, X21 : $i]:
% 0.22/0.46         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.22/0.46          | ((k7_relat_1 @ X20 @ X21) = (X20))
% 0.22/0.46          | ~ (v1_relat_1 @ X20))),
% 0.22/0.46      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.22/0.46  thf('3', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.46          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.46  thf(fc3_funct_1, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.22/0.46       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.46  thf('4', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.22/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.46  thf('5', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.46          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.22/0.46      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.46  thf('6', plain,
% 0.22/0.46      (((k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B)
% 0.22/0.46         = (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['0', '5'])).
% 0.22/0.46  thf(t90_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ B ) =>
% 0.22/0.46       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.22/0.46         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.46  thf('7', plain,
% 0.22/0.46      (![X18 : $i, X19 : $i]:
% 0.22/0.46         (((k1_relat_1 @ (k7_relat_1 @ X18 @ X19))
% 0.22/0.46            = (k3_xboole_0 @ (k1_relat_1 @ X18) @ X19))
% 0.22/0.46          | ~ (v1_relat_1 @ X18))),
% 0.22/0.46      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.22/0.46  thf('8', plain,
% 0.22/0.46      ((((k1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.22/0.46          = (k3_xboole_0 @ 
% 0.22/0.46             (k1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C))) @ sk_B))
% 0.22/0.46        | ~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.22/0.46      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.46  thf('9', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.22/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.46  thf('10', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.22/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.46  thf(commutativity_k2_tarski, axiom,
% 0.22/0.46    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.46  thf('11', plain,
% 0.22/0.46      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.22/0.46      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.46  thf(t12_setfam_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.46  thf('12', plain,
% 0.22/0.46      (![X10 : $i, X11 : $i]:
% 0.22/0.46         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.22/0.46      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.46  thf('13', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.46      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.46  thf('14', plain,
% 0.22/0.46      (![X10 : $i, X11 : $i]:
% 0.22/0.46         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.22/0.46      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.46  thf('15', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.46      inference('sup+', [status(thm)], ['13', '14'])).
% 0.22/0.46  thf('16', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.22/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.46  thf('17', plain,
% 0.22/0.46      (((k10_relat_1 @ sk_A @ sk_C)
% 0.22/0.46         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.22/0.46      inference('demod', [status(thm)], ['8', '9', '10', '15', '16'])).
% 0.22/0.46  thf(t139_funct_1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ C ) =>
% 0.22/0.46       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.22/0.46         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.22/0.46  thf('18', plain,
% 0.22/0.46      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.46         (((k10_relat_1 @ (k7_relat_1 @ X25 @ X24) @ X26)
% 0.22/0.46            = (k3_xboole_0 @ X24 @ (k10_relat_1 @ X25 @ X26)))
% 0.22/0.46          | ~ (v1_relat_1 @ X25))),
% 0.22/0.46      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.22/0.46  thf('19', plain,
% 0.22/0.46      (((k10_relat_1 @ sk_A @ sk_C)
% 0.22/0.46         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('20', plain,
% 0.22/0.46      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.22/0.46          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.22/0.46        | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.46  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('22', plain,
% 0.22/0.46      (((k10_relat_1 @ sk_A @ sk_C)
% 0.22/0.46         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.22/0.46      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.46  thf('23', plain, ($false),
% 0.22/0.46      inference('simplify_reflect-', [status(thm)], ['17', '22'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
