%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KVhiaiwRRg

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:31 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   50 (  57 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  344 ( 448 expanded)
%              Number of equality atoms :   29 (  36 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k3_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X17 @ ( k2_relat_1 @ X18 ) )
      | ( ( k9_relat_1 @ X18 @ ( k10_relat_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ ( k1_relat_1 @ X16 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

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

thf('17',plain,
    ( ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
     != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','22','23','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KVhiaiwRRg
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:27:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 221 iterations in 0.112s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.39/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.57  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.39/0.57  thf(t168_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( k10_relat_1 @ B @ A ) =
% 0.39/0.57         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.39/0.57  thf('0', plain,
% 0.39/0.57      (![X14 : $i, X15 : $i]:
% 0.39/0.57         (((k10_relat_1 @ X14 @ X15)
% 0.39/0.57            = (k10_relat_1 @ X14 @ (k3_xboole_0 @ (k2_relat_1 @ X14) @ X15)))
% 0.39/0.57          | ~ (v1_relat_1 @ X14))),
% 0.39/0.57      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.39/0.57  thf(d10_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.57  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.57      inference('simplify', [status(thm)], ['1'])).
% 0.39/0.57  thf(t108_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k3_xboole_0 @ X3 @ X5) @ X4))),
% 0.39/0.57      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.39/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.57  thf(t147_funct_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.57       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.39/0.57         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X17 : $i, X18 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X17 @ (k2_relat_1 @ X18))
% 0.39/0.57          | ((k9_relat_1 @ X18 @ (k10_relat_1 @ X18 @ X17)) = (X17))
% 0.39/0.57          | ~ (v1_funct_1 @ X18)
% 0.39/0.57          | ~ (v1_relat_1 @ X18))),
% 0.39/0.57      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X0)
% 0.39/0.57          | ~ (v1_funct_1 @ X0)
% 0.39/0.57          | ((k9_relat_1 @ X0 @ 
% 0.39/0.57              (k10_relat_1 @ X0 @ (k3_xboole_0 @ (k2_relat_1 @ X0) @ X1)))
% 0.39/0.57              = (k3_xboole_0 @ (k2_relat_1 @ X0) @ X1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 0.39/0.57            = (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0))
% 0.39/0.57          | ~ (v1_relat_1 @ X1)
% 0.39/0.57          | ~ (v1_funct_1 @ X1)
% 0.39/0.57          | ~ (v1_relat_1 @ X1))),
% 0.39/0.57      inference('sup+', [status(thm)], ['0', '6'])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v1_funct_1 @ X1)
% 0.39/0.57          | ~ (v1_relat_1 @ X1)
% 0.39/0.57          | ((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 0.39/0.57              = (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['7'])).
% 0.39/0.57  thf(t98_relat_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X16 : $i]:
% 0.39/0.57         (((k7_relat_1 @ X16 @ (k1_relat_1 @ X16)) = (X16))
% 0.39/0.57          | ~ (v1_relat_1 @ X16))),
% 0.39/0.57      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.39/0.57  thf(t148_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i]:
% 0.39/0.57         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.39/0.57          | ~ (v1_relat_1 @ X12))),
% 0.39/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.39/0.57          | ~ (v1_relat_1 @ X0)
% 0.39/0.57          | ~ (v1_relat_1 @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X0)
% 0.39/0.57          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.39/0.57      inference('simplify', [status(thm)], ['11'])).
% 0.39/0.57  thf(t148_funct_1, conjecture,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.57       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.39/0.57         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i]:
% 0.39/0.57        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.57          ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.39/0.57            ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t148_funct_1])).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.39/0.57         != (k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      ((((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.39/0.57          != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.39/0.57        | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.57  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.39/0.57         != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.39/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      ((((k3_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)
% 0.39/0.57          != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.39/0.57        | ~ (v1_relat_1 @ sk_B)
% 0.39/0.57        | ~ (v1_funct_1 @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['8', '16'])).
% 0.39/0.57  thf(commutativity_k2_tarski, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.39/0.57      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.39/0.57  thf(t12_setfam_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X10 : $i, X11 : $i]:
% 0.39/0.57         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.39/0.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('sup+', [status(thm)], ['18', '19'])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (![X10 : $i, X11 : $i]:
% 0.39/0.57         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.39/0.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('sup+', [status(thm)], ['20', '21'])).
% 0.39/0.57  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B))
% 0.39/0.57         != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.39/0.57      inference('demod', [status(thm)], ['17', '22', '23', '24'])).
% 0.39/0.57  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
