%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.k4uP6WVCKX

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:36 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   52 (  58 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :   15
%              Number of atoms          :  496 ( 598 expanded)
%              Number of equality atoms :   30 (  36 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) @ X14 )
        = ( k9_relat_1 @ X16 @ X14 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) @ X21 )
        = ( k3_xboole_0 @ X19 @ ( k10_relat_1 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X11: $i] :
      ( ( ( k9_relat_1 @ X11 @ ( k1_relat_1 @ X11 ) )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k9_relat_1 @ X23 @ ( k10_relat_1 @ X23 @ X22 ) )
        = ( k3_xboole_0 @ X22 @ ( k9_relat_1 @ X23 @ ( k1_relat_1 @ X23 ) ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) )
        = ( k3_xboole_0 @ X2 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) )
        = ( k3_xboole_0 @ X2 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) )
        = ( k3_xboole_0 @ X2 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) )
        = ( k3_xboole_0 @ X2 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t150_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t150_funct_1])).

thf('18',plain,(
    ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) )
 != ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) )
 != ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) )
     != ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) )
 != ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) )
     != ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) )
 != ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.k4uP6WVCKX
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 229 iterations in 0.132s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.39/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.58  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.39/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.58  thf(t148_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ B ) =>
% 0.39/0.58       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      (![X12 : $i, X13 : $i]:
% 0.39/0.58         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.39/0.58          | ~ (v1_relat_1 @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.39/0.58  thf(t17_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.39/0.58      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.39/0.58  thf(t162_relat_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ A ) =>
% 0.39/0.58       ( ![B:$i,C:$i]:
% 0.39/0.58         ( ( r1_tarski @ B @ C ) =>
% 0.39/0.58           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.39/0.58             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.58         (~ (r1_tarski @ X14 @ X15)
% 0.39/0.58          | ((k9_relat_1 @ (k7_relat_1 @ X16 @ X15) @ X14)
% 0.39/0.58              = (k9_relat_1 @ X16 @ X14))
% 0.39/0.58          | ~ (v1_relat_1 @ X16))),
% 0.39/0.58      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X2)
% 0.39/0.58          | ((k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 0.39/0.58              = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.58  thf(fc8_funct_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.58       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.39/0.58         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i]:
% 0.39/0.58         (~ (v1_funct_1 @ X17)
% 0.39/0.58          | ~ (v1_relat_1 @ X17)
% 0.39/0.58          | (v1_funct_1 @ (k7_relat_1 @ X17 @ X18)))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.39/0.58  thf(dt_k7_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X9 : $i, X10 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X9) | (v1_relat_1 @ (k7_relat_1 @ X9 @ X10)))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.39/0.58  thf(t139_funct_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ C ) =>
% 0.39/0.58       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.39/0.58         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.58         (((k10_relat_1 @ (k7_relat_1 @ X20 @ X19) @ X21)
% 0.39/0.58            = (k3_xboole_0 @ X19 @ (k10_relat_1 @ X20 @ X21)))
% 0.39/0.58          | ~ (v1_relat_1 @ X20))),
% 0.39/0.58      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.39/0.58  thf(t146_relat_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ A ) =>
% 0.39/0.58       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X11 : $i]:
% 0.39/0.58         (((k9_relat_1 @ X11 @ (k1_relat_1 @ X11)) = (k2_relat_1 @ X11))
% 0.39/0.58          | ~ (v1_relat_1 @ X11))),
% 0.39/0.58      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.39/0.58  thf(t148_funct_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.58       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.39/0.58         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X22 : $i, X23 : $i]:
% 0.39/0.58         (((k9_relat_1 @ X23 @ (k10_relat_1 @ X23 @ X22))
% 0.39/0.58            = (k3_xboole_0 @ X22 @ (k9_relat_1 @ X23 @ (k1_relat_1 @ X23))))
% 0.39/0.58          | ~ (v1_funct_1 @ X23)
% 0.39/0.58          | ~ (v1_relat_1 @ X23))),
% 0.39/0.58      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.39/0.58            = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.39/0.58              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.39/0.58      inference('simplify', [status(thm)], ['9'])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (((k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ 
% 0.39/0.58            (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 0.39/0.58            = (k3_xboole_0 @ X0 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X2))))
% 0.39/0.58          | ~ (v1_relat_1 @ X1)
% 0.39/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2))
% 0.39/0.58          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['6', '10'])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X1)
% 0.39/0.58          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ X1)
% 0.39/0.58          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.39/0.58              (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2)))
% 0.39/0.58              = (k3_xboole_0 @ X2 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['5', '11'])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.39/0.58            (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2)))
% 0.39/0.58            = (k3_xboole_0 @ X2 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.39/0.58          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ X1))),
% 0.39/0.58      inference('simplify', [status(thm)], ['12'])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X1)
% 0.39/0.58          | ~ (v1_funct_1 @ X1)
% 0.39/0.58          | ~ (v1_relat_1 @ X1)
% 0.39/0.58          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.39/0.58              (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2)))
% 0.39/0.58              = (k3_xboole_0 @ X2 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['4', '13'])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.39/0.58            (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2)))
% 0.39/0.58            = (k3_xboole_0 @ X2 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.39/0.58          | ~ (v1_funct_1 @ X1)
% 0.39/0.58          | ~ (v1_relat_1 @ X1))),
% 0.39/0.58      inference('simplify', [status(thm)], ['14'])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (((k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 0.39/0.58            = (k3_xboole_0 @ X0 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X2))))
% 0.39/0.58          | ~ (v1_relat_1 @ X1)
% 0.39/0.58          | ~ (v1_relat_1 @ X1)
% 0.39/0.58          | ~ (v1_funct_1 @ X1))),
% 0.39/0.58      inference('sup+', [status(thm)], ['3', '15'])).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (v1_funct_1 @ X1)
% 0.39/0.58          | ~ (v1_relat_1 @ X1)
% 0.39/0.58          | ((k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 0.39/0.58              = (k3_xboole_0 @ X0 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X2)))))),
% 0.39/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.39/0.58  thf(t150_funct_1, conjecture,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.39/0.58       ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) =
% 0.39/0.58         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.58        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.39/0.58          ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) =
% 0.39/0.58            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t150_funct_1])).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (((k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B)))
% 0.39/0.58         != (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (((k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B)))
% 0.39/0.58         != (k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['18', '19'])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      ((((k3_xboole_0 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))
% 0.39/0.58          != (k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A)))
% 0.39/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.58        | ~ (v1_funct_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['17', '20'])).
% 0.39/0.58  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (((k3_xboole_0 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))
% 0.39/0.58         != (k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      ((((k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A))
% 0.39/0.58          != (k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A)))
% 0.39/0.58        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['0', '24'])).
% 0.39/0.58  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      (((k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A))
% 0.39/0.58         != (k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['25', '26'])).
% 0.39/0.58  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
