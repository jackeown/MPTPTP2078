%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JBm7c8LcAd

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:40 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   49 (  54 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  293 ( 373 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_xboole_0 @ X10 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ X0 ) @ ( k4_xboole_0 @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X9 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X14 @ X13 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','11','16'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X27 @ X26 ) @ X28 )
        = ( k3_xboole_0 @ X26 @ ( k10_relat_1 @ X27 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JBm7c8LcAd
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:52:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 209 iterations in 0.092s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.57  thf(t175_funct_2, conjecture,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.57       ( ![B:$i,C:$i]:
% 0.37/0.57         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.37/0.57           ( ( k10_relat_1 @ A @ C ) =
% 0.37/0.57             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i]:
% 0.37/0.57        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.57          ( ![B:$i,C:$i]:
% 0.37/0.57            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.37/0.57              ( ( k10_relat_1 @ A @ C ) =
% 0.37/0.57                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.37/0.57  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t36_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.37/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.57  thf(t1_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.57       ( r1_tarski @ A @ C ) ))).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (~ (r1_tarski @ X0 @ X1)
% 0.37/0.57          | ~ (r1_tarski @ X1 @ X2)
% 0.37/0.57          | (r1_tarski @ X0 @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (r1_tarski @ (k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ X0) @ sk_B)),
% 0.37/0.57      inference('sup-', [status(thm)], ['0', '3'])).
% 0.37/0.57  thf(t85_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.57         (~ (r1_tarski @ X10 @ X11)
% 0.37/0.57          | (r1_xboole_0 @ X10 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (r1_xboole_0 @ (k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ X0) @ 
% 0.37/0.57          (k4_xboole_0 @ X1 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.57  thf(t66_xboole_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.37/0.57       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X9 @ X9))),
% 0.37/0.57      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      (((k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.57  thf(t48_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      (![X6 : $i, X7 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.37/0.57           = (k3_xboole_0 @ X6 @ X7))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (((k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ k1_xboole_0)
% 0.37/0.57         = (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.37/0.57      inference('sup+', [status(thm)], ['8', '9'])).
% 0.37/0.57  thf(t3_boole, axiom,
% 0.37/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.57  thf('11', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.57  thf(commutativity_k2_tarski, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (![X13 : $i, X14 : $i]:
% 0.37/0.57         ((k2_tarski @ X14 @ X13) = (k2_tarski @ X13 @ X14))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.57  thf(t12_setfam_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      (![X24 : $i, X25 : $i]:
% 0.37/0.57         ((k1_setfam_1 @ (k2_tarski @ X24 @ X25)) = (k3_xboole_0 @ X24 @ X25))),
% 0.37/0.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X24 : $i, X25 : $i]:
% 0.37/0.57         ((k1_setfam_1 @ (k2_tarski @ X24 @ X25)) = (k3_xboole_0 @ X24 @ X25))),
% 0.37/0.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      (((k10_relat_1 @ sk_A @ sk_C)
% 0.37/0.57         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.37/0.57      inference('demod', [status(thm)], ['10', '11', '16'])).
% 0.37/0.57  thf(t139_funct_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ C ) =>
% 0.37/0.57       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.37/0.57         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.37/0.57         (((k10_relat_1 @ (k7_relat_1 @ X27 @ X26) @ X28)
% 0.37/0.57            = (k3_xboole_0 @ X26 @ (k10_relat_1 @ X27 @ X28)))
% 0.37/0.57          | ~ (v1_relat_1 @ X27))),
% 0.37/0.57      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (((k10_relat_1 @ sk_A @ sk_C)
% 0.37/0.57         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.37/0.57          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.37/0.57        | ~ (v1_relat_1 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.57  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      (((k10_relat_1 @ sk_A @ sk_C)
% 0.37/0.57         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.37/0.57      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.57  thf('23', plain, ($false),
% 0.37/0.57      inference('simplify_reflect-', [status(thm)], ['17', '22'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
