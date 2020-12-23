%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xk6RM1MPD6

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:30 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   67 (  80 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  544 ( 702 expanded)
%              Number of equality atoms :   42 (  55 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t126_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k9_relat_1 @ ( k8_relat_1 @ X20 @ X21 ) @ X22 )
        = ( k3_xboole_0 @ X20 @ ( k9_relat_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t126_funct_1])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X23 @ ( k10_relat_1 @ X23 @ X24 ) ) @ X24 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t120_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
          = A ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ ( k2_relat_1 @ X10 ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X9 @ X10 ) )
        = X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t120_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X8 @ X7 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X7 ) @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(fc9_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k8_relat_1 @ X12 @ X11 )
        = ( k5_relat_1 @ X11 @ ( k6_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('18',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k10_relat_1 @ X15 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X13: $i] :
      ( ( ( k9_relat_1 @ X13 @ ( k1_relat_1 @ X13 ) )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t147_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
         => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t147_funct_1])).

thf('31',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) )
     != sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ ( k2_relat_1 @ X10 ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X9 @ X10 ) )
        = X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t120_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['32','37','38','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xk6RM1MPD6
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 105 iterations in 0.149s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.40/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.40/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.62  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.40/0.62  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.40/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.40/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.62  thf(t126_funct_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.62       ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.40/0.62         ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.40/0.62  thf('0', plain,
% 0.40/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.40/0.62         (((k9_relat_1 @ (k8_relat_1 @ X20 @ X21) @ X22)
% 0.40/0.62            = (k3_xboole_0 @ X20 @ (k9_relat_1 @ X21 @ X22)))
% 0.40/0.62          | ~ (v1_funct_1 @ X21)
% 0.40/0.62          | ~ (v1_relat_1 @ X21))),
% 0.40/0.62      inference('cnf', [status(esa)], [t126_funct_1])).
% 0.40/0.62  thf(t145_funct_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.62       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.40/0.62  thf('1', plain,
% 0.40/0.62      (![X23 : $i, X24 : $i]:
% 0.40/0.62         ((r1_tarski @ (k9_relat_1 @ X23 @ (k10_relat_1 @ X23 @ X24)) @ X24)
% 0.40/0.62          | ~ (v1_funct_1 @ X23)
% 0.40/0.62          | ~ (v1_relat_1 @ X23))),
% 0.40/0.62      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.40/0.62  thf(t71_relat_1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.40/0.62       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.40/0.62  thf('2', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.40/0.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.40/0.62  thf(t120_relat_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ B ) =>
% 0.40/0.62       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.40/0.62         ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) = ( A ) ) ) ))).
% 0.40/0.62  thf('3', plain,
% 0.40/0.62      (![X9 : $i, X10 : $i]:
% 0.40/0.62         (~ (r1_tarski @ X9 @ (k2_relat_1 @ X10))
% 0.40/0.62          | ((k2_relat_1 @ (k8_relat_1 @ X9 @ X10)) = (X9))
% 0.40/0.62          | ~ (v1_relat_1 @ X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [t120_relat_1])).
% 0.40/0.62  thf('4', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (r1_tarski @ X1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.40/0.62          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) = (X1)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.62  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.40/0.62  thf('5', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.40/0.62  thf('6', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (r1_tarski @ X1 @ X0)
% 0.40/0.62          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) = (X1)))),
% 0.40/0.62      inference('demod', [status(thm)], ['4', '5'])).
% 0.40/0.62  thf('7', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.40/0.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.40/0.62  thf(t119_relat_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ B ) =>
% 0.40/0.62       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.40/0.62         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.40/0.62  thf('8', plain,
% 0.40/0.62      (![X7 : $i, X8 : $i]:
% 0.40/0.62         (((k2_relat_1 @ (k8_relat_1 @ X8 @ X7))
% 0.40/0.62            = (k3_xboole_0 @ (k2_relat_1 @ X7) @ X8))
% 0.40/0.62          | ~ (v1_relat_1 @ X7))),
% 0.40/0.62      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.40/0.62  thf('9', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.40/0.62            = (k3_xboole_0 @ X0 @ X1))
% 0.40/0.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.40/0.62      inference('sup+', [status(thm)], ['7', '8'])).
% 0.40/0.62  thf('10', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.40/0.62  thf('11', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.40/0.62           = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.62  thf('12', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (r1_tarski @ X1 @ X0) | ((k3_xboole_0 @ X0 @ X1) = (X1)))),
% 0.40/0.62      inference('demod', [status(thm)], ['6', '11'])).
% 0.40/0.62  thf('13', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X1)
% 0.40/0.62          | ~ (v1_funct_1 @ X1)
% 0.40/0.62          | ((k3_xboole_0 @ X0 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)))
% 0.40/0.62              = (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['1', '12'])).
% 0.40/0.62  thf('14', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (((k9_relat_1 @ (k8_relat_1 @ X0 @ X1) @ (k10_relat_1 @ X1 @ X0))
% 0.40/0.62            = (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)))
% 0.40/0.62          | ~ (v1_relat_1 @ X1)
% 0.40/0.62          | ~ (v1_funct_1 @ X1)
% 0.40/0.62          | ~ (v1_funct_1 @ X1)
% 0.40/0.62          | ~ (v1_relat_1 @ X1))),
% 0.40/0.62      inference('sup+', [status(thm)], ['0', '13'])).
% 0.40/0.62  thf('15', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (v1_funct_1 @ X1)
% 0.40/0.62          | ~ (v1_relat_1 @ X1)
% 0.40/0.62          | ((k9_relat_1 @ (k8_relat_1 @ X0 @ X1) @ (k10_relat_1 @ X1 @ X0))
% 0.40/0.62              = (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))))),
% 0.40/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.40/0.62  thf(fc9_funct_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.62       ( ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) & 
% 0.40/0.62         ( v1_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ))).
% 0.40/0.62  thf('16', plain,
% 0.40/0.62      (![X18 : $i, X19 : $i]:
% 0.40/0.62         ((v1_relat_1 @ (k8_relat_1 @ X18 @ X19))
% 0.40/0.62          | ~ (v1_funct_1 @ X19)
% 0.40/0.62          | ~ (v1_relat_1 @ X19))),
% 0.40/0.62      inference('cnf', [status(esa)], [fc9_funct_1])).
% 0.40/0.62  thf(t123_relat_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ B ) =>
% 0.40/0.62       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.40/0.62  thf('17', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i]:
% 0.40/0.62         (((k8_relat_1 @ X12 @ X11) = (k5_relat_1 @ X11 @ (k6_relat_1 @ X12)))
% 0.40/0.62          | ~ (v1_relat_1 @ X11))),
% 0.40/0.62      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.40/0.62  thf('18', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.40/0.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.40/0.62  thf(t182_relat_1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ A ) =>
% 0.40/0.62       ( ![B:$i]:
% 0.40/0.62         ( ( v1_relat_1 @ B ) =>
% 0.40/0.62           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.40/0.62             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.40/0.62  thf('19', plain,
% 0.40/0.62      (![X14 : $i, X15 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X14)
% 0.40/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 0.40/0.62              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 0.40/0.62          | ~ (v1_relat_1 @ X15))),
% 0.40/0.62      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.40/0.62  thf('20', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.40/0.62            = (k10_relat_1 @ X1 @ X0))
% 0.40/0.62          | ~ (v1_relat_1 @ X1)
% 0.40/0.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.40/0.62      inference('sup+', [status(thm)], ['18', '19'])).
% 0.40/0.62  thf('21', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.40/0.62  thf('22', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.40/0.62            = (k10_relat_1 @ X1 @ X0))
% 0.40/0.62          | ~ (v1_relat_1 @ X1))),
% 0.40/0.62      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.62  thf('23', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (((k1_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k10_relat_1 @ X0 @ X1))
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['17', '22'])).
% 0.40/0.62  thf('24', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X0)
% 0.40/0.62          | ((k1_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k10_relat_1 @ X0 @ X1)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['23'])).
% 0.40/0.62  thf(t146_relat_1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ A ) =>
% 0.40/0.62       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.40/0.62  thf('25', plain,
% 0.40/0.62      (![X13 : $i]:
% 0.40/0.62         (((k9_relat_1 @ X13 @ (k1_relat_1 @ X13)) = (k2_relat_1 @ X13))
% 0.40/0.62          | ~ (v1_relat_1 @ X13))),
% 0.40/0.62      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.40/0.62  thf('26', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (((k9_relat_1 @ (k8_relat_1 @ X0 @ X1) @ (k10_relat_1 @ X1 @ X0))
% 0.40/0.62            = (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)))
% 0.40/0.62          | ~ (v1_relat_1 @ X1)
% 0.40/0.62          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1)))),
% 0.40/0.62      inference('sup+', [status(thm)], ['24', '25'])).
% 0.40/0.62  thf('27', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ((k9_relat_1 @ (k8_relat_1 @ X1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.40/0.62              = (k2_relat_1 @ (k8_relat_1 @ X1 @ X0))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['16', '26'])).
% 0.40/0.62  thf('28', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (((k9_relat_1 @ (k8_relat_1 @ X1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.40/0.62            = (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('simplify', [status(thm)], ['27'])).
% 0.40/0.62  thf('29', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 0.40/0.62            = (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)))
% 0.40/0.62          | ~ (v1_relat_1 @ X1)
% 0.40/0.62          | ~ (v1_funct_1 @ X1)
% 0.40/0.62          | ~ (v1_relat_1 @ X1)
% 0.40/0.62          | ~ (v1_funct_1 @ X1))),
% 0.40/0.62      inference('sup+', [status(thm)], ['15', '28'])).
% 0.40/0.62  thf('30', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (v1_funct_1 @ X1)
% 0.40/0.62          | ~ (v1_relat_1 @ X1)
% 0.40/0.62          | ((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 0.40/0.62              = (k2_relat_1 @ (k8_relat_1 @ X0 @ X1))))),
% 0.40/0.62      inference('simplify', [status(thm)], ['29'])).
% 0.40/0.62  thf(t147_funct_1, conjecture,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.62       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.40/0.62         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.40/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.62    (~( ![A:$i,B:$i]:
% 0.40/0.62        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.62          ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.40/0.62            ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t147_funct_1])).
% 0.40/0.62  thf('31', plain,
% 0.40/0.62      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('32', plain,
% 0.40/0.62      ((((k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) != (sk_A))
% 0.40/0.62        | ~ (v1_relat_1 @ sk_B)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.62  thf('33', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('34', plain,
% 0.40/0.62      (![X9 : $i, X10 : $i]:
% 0.40/0.62         (~ (r1_tarski @ X9 @ (k2_relat_1 @ X10))
% 0.40/0.62          | ((k2_relat_1 @ (k8_relat_1 @ X9 @ X10)) = (X9))
% 0.40/0.62          | ~ (v1_relat_1 @ X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [t120_relat_1])).
% 0.40/0.62  thf('35', plain,
% 0.40/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.40/0.62        | ((k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) = (sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.62  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('37', plain, (((k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.40/0.62      inference('demod', [status(thm)], ['35', '36'])).
% 0.40/0.62  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('39', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('40', plain, (((sk_A) != (sk_A))),
% 0.40/0.62      inference('demod', [status(thm)], ['32', '37', '38', '39'])).
% 0.40/0.62  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.40/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
