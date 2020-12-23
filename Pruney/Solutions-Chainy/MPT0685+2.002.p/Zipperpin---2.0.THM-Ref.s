%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uRiJqZQSxR

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:07 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   59 (  69 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  421 ( 509 expanded)
%              Number of equality atoms :   38 (  45 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ X16 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k10_relat_1 @ X10 @ ( k10_relat_1 @ X9 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ X16 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
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
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ X16 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X21 ) @ ( k6_relat_1 @ X20 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['8','21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','24'])).

thf('26',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t139_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t139_funct_1])).

thf('30',plain,(
    ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
 != ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uRiJqZQSxR
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:37:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.57/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.76  % Solved by: fo/fo7.sh
% 0.57/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.76  % done 438 iterations in 0.307s
% 0.57/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.76  % SZS output start Refutation
% 0.57/0.76  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.57/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.57/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.76  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.57/0.76  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.57/0.76  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.57/0.76  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.57/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.57/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.57/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.57/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.57/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.57/0.76  thf(t94_relat_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( v1_relat_1 @ B ) =>
% 0.57/0.76       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.57/0.76  thf('0', plain,
% 0.57/0.76      (![X16 : $i, X17 : $i]:
% 0.57/0.76         (((k7_relat_1 @ X17 @ X16) = (k5_relat_1 @ (k6_relat_1 @ X16) @ X17))
% 0.57/0.76          | ~ (v1_relat_1 @ X17))),
% 0.57/0.76      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.57/0.76  thf(t181_relat_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( v1_relat_1 @ B ) =>
% 0.57/0.76       ( ![C:$i]:
% 0.57/0.76         ( ( v1_relat_1 @ C ) =>
% 0.57/0.76           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.57/0.76             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.57/0.76  thf('1', plain,
% 0.57/0.76      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.57/0.76         (~ (v1_relat_1 @ X9)
% 0.57/0.76          | ((k10_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 0.57/0.76              = (k10_relat_1 @ X10 @ (k10_relat_1 @ X9 @ X11)))
% 0.57/0.76          | ~ (v1_relat_1 @ X10))),
% 0.57/0.76      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.57/0.76  thf('2', plain,
% 0.57/0.76      (![X16 : $i, X17 : $i]:
% 0.57/0.76         (((k7_relat_1 @ X17 @ X16) = (k5_relat_1 @ (k6_relat_1 @ X16) @ X17))
% 0.57/0.76          | ~ (v1_relat_1 @ X17))),
% 0.57/0.76      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.57/0.76  thf(t71_relat_1, axiom,
% 0.57/0.76    (![A:$i]:
% 0.57/0.76     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.57/0.76       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.57/0.76  thf('3', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.57/0.76      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.57/0.76  thf(t182_relat_1, axiom,
% 0.57/0.76    (![A:$i]:
% 0.57/0.76     ( ( v1_relat_1 @ A ) =>
% 0.57/0.76       ( ![B:$i]:
% 0.57/0.76         ( ( v1_relat_1 @ B ) =>
% 0.57/0.76           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.57/0.76             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.57/0.76  thf('4', plain,
% 0.57/0.76      (![X12 : $i, X13 : $i]:
% 0.57/0.76         (~ (v1_relat_1 @ X12)
% 0.57/0.76          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.57/0.76              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 0.57/0.76          | ~ (v1_relat_1 @ X13))),
% 0.57/0.76      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.57/0.76  thf('5', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.57/0.76            = (k10_relat_1 @ X1 @ X0))
% 0.57/0.76          | ~ (v1_relat_1 @ X1)
% 0.57/0.76          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.57/0.76      inference('sup+', [status(thm)], ['3', '4'])).
% 0.57/0.76  thf(fc3_funct_1, axiom,
% 0.57/0.76    (![A:$i]:
% 0.57/0.76     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.57/0.76       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.57/0.76  thf('6', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.57/0.76      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.57/0.76  thf('7', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.57/0.76            = (k10_relat_1 @ X1 @ X0))
% 0.57/0.76          | ~ (v1_relat_1 @ X1))),
% 0.57/0.76      inference('demod', [status(thm)], ['5', '6'])).
% 0.57/0.76  thf('8', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.57/0.76            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.57/0.76          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.57/0.76          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.57/0.76      inference('sup+', [status(thm)], ['2', '7'])).
% 0.57/0.76  thf(commutativity_k2_tarski, axiom,
% 0.57/0.76    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.57/0.76  thf('9', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.57/0.76      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.57/0.76  thf(t12_setfam_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.57/0.76  thf('10', plain,
% 0.57/0.76      (![X7 : $i, X8 : $i]:
% 0.57/0.76         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.57/0.76      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.57/0.76  thf('11', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.76      inference('sup+', [status(thm)], ['9', '10'])).
% 0.57/0.76  thf('12', plain,
% 0.57/0.76      (![X7 : $i, X8 : $i]:
% 0.57/0.76         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.57/0.76      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.57/0.76  thf('13', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.76      inference('sup+', [status(thm)], ['11', '12'])).
% 0.57/0.76  thf('14', plain,
% 0.57/0.76      (![X16 : $i, X17 : $i]:
% 0.57/0.76         (((k7_relat_1 @ X17 @ X16) = (k5_relat_1 @ (k6_relat_1 @ X16) @ X17))
% 0.57/0.76          | ~ (v1_relat_1 @ X17))),
% 0.57/0.76      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.57/0.76  thf(t43_funct_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.57/0.76       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.57/0.76  thf('15', plain,
% 0.57/0.76      (![X20 : $i, X21 : $i]:
% 0.57/0.76         ((k5_relat_1 @ (k6_relat_1 @ X21) @ (k6_relat_1 @ X20))
% 0.57/0.76           = (k6_relat_1 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.57/0.76  thf('16', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.57/0.76            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.57/0.76          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.57/0.76      inference('sup+', [status(thm)], ['14', '15'])).
% 0.57/0.76  thf('17', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.57/0.76      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.57/0.76  thf('18', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.57/0.76           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.57/0.76      inference('demod', [status(thm)], ['16', '17'])).
% 0.57/0.76  thf('19', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.57/0.76           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.57/0.76      inference('sup+', [status(thm)], ['13', '18'])).
% 0.57/0.76  thf('20', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.57/0.76      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.57/0.76  thf('21', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.57/0.76           = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.76      inference('sup+', [status(thm)], ['19', '20'])).
% 0.57/0.76  thf('22', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.57/0.76      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.57/0.76  thf('23', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.57/0.76      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.57/0.76  thf('24', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         ((k3_xboole_0 @ X0 @ X1) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.57/0.76      inference('demod', [status(thm)], ['8', '21', '22', '23'])).
% 0.57/0.76  thf('25', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.76         (((k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))
% 0.57/0.76            = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 0.57/0.76          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 0.57/0.76          | ~ (v1_relat_1 @ X1))),
% 0.57/0.76      inference('sup+', [status(thm)], ['1', '24'])).
% 0.57/0.76  thf('26', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.57/0.76      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.57/0.76  thf('27', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.76         (((k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))
% 0.57/0.76            = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 0.57/0.76          | ~ (v1_relat_1 @ X1))),
% 0.57/0.76      inference('demod', [status(thm)], ['25', '26'])).
% 0.57/0.76  thf('28', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.76         (((k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))
% 0.57/0.76            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.57/0.76          | ~ (v1_relat_1 @ X1)
% 0.57/0.76          | ~ (v1_relat_1 @ X1))),
% 0.57/0.76      inference('sup+', [status(thm)], ['0', '27'])).
% 0.57/0.76  thf('29', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.76         (~ (v1_relat_1 @ X1)
% 0.57/0.76          | ((k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))
% 0.57/0.76              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)))),
% 0.57/0.76      inference('simplify', [status(thm)], ['28'])).
% 0.57/0.76  thf(t139_funct_1, conjecture,
% 0.57/0.76    (![A:$i,B:$i,C:$i]:
% 0.57/0.76     ( ( v1_relat_1 @ C ) =>
% 0.57/0.76       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.57/0.76         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.57/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.76    (~( ![A:$i,B:$i,C:$i]:
% 0.57/0.76        ( ( v1_relat_1 @ C ) =>
% 0.57/0.76          ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.57/0.76            ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.57/0.76    inference('cnf.neg', [status(esa)], [t139_funct_1])).
% 0.57/0.76  thf('30', plain,
% 0.57/0.76      (((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.57/0.76         != (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B)))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('31', plain,
% 0.57/0.76      ((((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.57/0.76          != (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B))
% 0.57/0.76        | ~ (v1_relat_1 @ sk_C))),
% 0.57/0.76      inference('sup-', [status(thm)], ['29', '30'])).
% 0.57/0.76  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('33', plain,
% 0.57/0.76      (((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.57/0.76         != (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 0.57/0.76      inference('demod', [status(thm)], ['31', '32'])).
% 0.57/0.76  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 0.57/0.76  
% 0.57/0.76  % SZS output end Refutation
% 0.57/0.76  
% 0.60/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
