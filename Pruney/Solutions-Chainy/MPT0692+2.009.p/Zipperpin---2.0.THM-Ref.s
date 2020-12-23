%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mDHeKHdVKB

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:30 EST 2020

% Result     : Theorem 4.55s
% Output     : Refutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :   62 (  77 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  485 ( 687 expanded)
%              Number of equality atoms :   36 (  51 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ X15 @ ( k6_subset_1 @ X16 @ X17 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X15 @ X16 ) @ ( k10_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X11 @ X12 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( r1_tarski @ X20 @ ( k10_relat_1 @ X21 @ ( k9_relat_1 @ X21 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k6_subset_1 @ ( k10_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k6_subset_1 @ X0 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k6_subset_1 @ X0 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

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

thf('11',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k6_subset_1 @ X6 @ X8 ) @ X7 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t174_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( r1_tarski @ X13 @ ( k2_relat_1 @ X14 ) )
      | ( ( k10_relat_1 @ X14 @ X13 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t174_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k6_subset_1 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
       != k1_xboole_0 )
      | ( ( k6_subset_1 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k6_subset_1 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    r1_tarski @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X18 @ ( k10_relat_1 @ X18 @ X19 ) ) @ X19 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A
      = ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( sk_A
    = ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mDHeKHdVKB
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:40:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 4.55/4.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.55/4.76  % Solved by: fo/fo7.sh
% 4.55/4.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.55/4.76  % done 6339 iterations in 4.299s
% 4.55/4.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.55/4.76  % SZS output start Refutation
% 4.55/4.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.55/4.76  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 4.55/4.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.55/4.76  thf(sk_B_type, type, sk_B: $i).
% 4.55/4.76  thf(sk_A_type, type, sk_A: $i).
% 4.55/4.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.55/4.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.55/4.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.55/4.76  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 4.55/4.76  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 4.55/4.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.55/4.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.55/4.76  thf(t138_funct_1, axiom,
% 4.55/4.76    (![A:$i,B:$i,C:$i]:
% 4.55/4.76     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 4.55/4.76       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 4.55/4.76         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 4.55/4.76  thf('0', plain,
% 4.55/4.76      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.55/4.76         (((k10_relat_1 @ X15 @ (k6_subset_1 @ X16 @ X17))
% 4.55/4.76            = (k6_subset_1 @ (k10_relat_1 @ X15 @ X16) @ 
% 4.55/4.76               (k10_relat_1 @ X15 @ X17)))
% 4.55/4.76          | ~ (v1_funct_1 @ X15)
% 4.55/4.76          | ~ (v1_relat_1 @ X15))),
% 4.55/4.76      inference('cnf', [status(esa)], [t138_funct_1])).
% 4.55/4.76  thf(t167_relat_1, axiom,
% 4.55/4.76    (![A:$i,B:$i]:
% 4.55/4.76     ( ( v1_relat_1 @ B ) =>
% 4.55/4.76       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 4.55/4.76  thf('1', plain,
% 4.55/4.76      (![X11 : $i, X12 : $i]:
% 4.55/4.76         ((r1_tarski @ (k10_relat_1 @ X11 @ X12) @ (k1_relat_1 @ X11))
% 4.55/4.76          | ~ (v1_relat_1 @ X11))),
% 4.55/4.76      inference('cnf', [status(esa)], [t167_relat_1])).
% 4.55/4.76  thf(t146_funct_1, axiom,
% 4.55/4.76    (![A:$i,B:$i]:
% 4.55/4.76     ( ( v1_relat_1 @ B ) =>
% 4.55/4.76       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 4.55/4.76         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 4.55/4.76  thf('2', plain,
% 4.55/4.76      (![X20 : $i, X21 : $i]:
% 4.55/4.76         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 4.55/4.76          | (r1_tarski @ X20 @ (k10_relat_1 @ X21 @ (k9_relat_1 @ X21 @ X20)))
% 4.55/4.76          | ~ (v1_relat_1 @ X21))),
% 4.55/4.76      inference('cnf', [status(esa)], [t146_funct_1])).
% 4.55/4.76  thf('3', plain,
% 4.55/4.76      (![X0 : $i, X1 : $i]:
% 4.55/4.76         (~ (v1_relat_1 @ X0)
% 4.55/4.76          | ~ (v1_relat_1 @ X0)
% 4.55/4.76          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ 
% 4.55/4.76             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1)))))),
% 4.55/4.76      inference('sup-', [status(thm)], ['1', '2'])).
% 4.55/4.76  thf('4', plain,
% 4.55/4.76      (![X0 : $i, X1 : $i]:
% 4.55/4.76         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ 
% 4.55/4.76           (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))))
% 4.55/4.76          | ~ (v1_relat_1 @ X0))),
% 4.55/4.76      inference('simplify', [status(thm)], ['3'])).
% 4.55/4.76  thf(l32_xboole_1, axiom,
% 4.55/4.76    (![A:$i,B:$i]:
% 4.55/4.76     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.55/4.76  thf('5', plain,
% 4.55/4.76      (![X3 : $i, X5 : $i]:
% 4.55/4.76         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 4.55/4.76      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.55/4.76  thf(redefinition_k6_subset_1, axiom,
% 4.55/4.76    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 4.55/4.76  thf('6', plain,
% 4.55/4.76      (![X9 : $i, X10 : $i]:
% 4.55/4.76         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 4.55/4.76      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.55/4.76  thf('7', plain,
% 4.55/4.76      (![X3 : $i, X5 : $i]:
% 4.55/4.76         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 4.55/4.76      inference('demod', [status(thm)], ['5', '6'])).
% 4.55/4.76  thf('8', plain,
% 4.55/4.76      (![X0 : $i, X1 : $i]:
% 4.55/4.76         (~ (v1_relat_1 @ X1)
% 4.55/4.76          | ((k6_subset_1 @ (k10_relat_1 @ X1 @ X0) @ 
% 4.55/4.76              (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))))
% 4.55/4.76              = (k1_xboole_0)))),
% 4.55/4.76      inference('sup-', [status(thm)], ['4', '7'])).
% 4.55/4.76  thf('9', plain,
% 4.55/4.76      (![X0 : $i, X1 : $i]:
% 4.55/4.76         (((k10_relat_1 @ X1 @ 
% 4.55/4.76            (k6_subset_1 @ X0 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))))
% 4.55/4.76            = (k1_xboole_0))
% 4.55/4.76          | ~ (v1_relat_1 @ X1)
% 4.55/4.76          | ~ (v1_funct_1 @ X1)
% 4.55/4.76          | ~ (v1_relat_1 @ X1))),
% 4.55/4.76      inference('sup+', [status(thm)], ['0', '8'])).
% 4.55/4.76  thf('10', plain,
% 4.55/4.76      (![X0 : $i, X1 : $i]:
% 4.55/4.76         (~ (v1_funct_1 @ X1)
% 4.55/4.76          | ~ (v1_relat_1 @ X1)
% 4.55/4.76          | ((k10_relat_1 @ X1 @ 
% 4.55/4.76              (k6_subset_1 @ X0 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))))
% 4.55/4.76              = (k1_xboole_0)))),
% 4.55/4.76      inference('simplify', [status(thm)], ['9'])).
% 4.55/4.76  thf(t147_funct_1, conjecture,
% 4.55/4.76    (![A:$i,B:$i]:
% 4.55/4.76     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.55/4.76       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 4.55/4.76         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 4.55/4.76  thf(zf_stmt_0, negated_conjecture,
% 4.55/4.76    (~( ![A:$i,B:$i]:
% 4.55/4.76        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.55/4.76          ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 4.55/4.76            ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 4.55/4.76    inference('cnf.neg', [status(esa)], [t147_funct_1])).
% 4.55/4.76  thf('11', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 4.55/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.76  thf(t109_xboole_1, axiom,
% 4.55/4.76    (![A:$i,B:$i,C:$i]:
% 4.55/4.76     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 4.55/4.76  thf('12', plain,
% 4.55/4.76      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.55/4.76         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k4_xboole_0 @ X6 @ X8) @ X7))),
% 4.55/4.76      inference('cnf', [status(esa)], [t109_xboole_1])).
% 4.55/4.76  thf('13', plain,
% 4.55/4.76      (![X9 : $i, X10 : $i]:
% 4.55/4.76         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 4.55/4.76      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.55/4.76  thf('14', plain,
% 4.55/4.76      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.55/4.76         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k6_subset_1 @ X6 @ X8) @ X7))),
% 4.55/4.76      inference('demod', [status(thm)], ['12', '13'])).
% 4.55/4.76  thf('15', plain,
% 4.55/4.76      (![X0 : $i]:
% 4.55/4.76         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_B))),
% 4.55/4.76      inference('sup-', [status(thm)], ['11', '14'])).
% 4.55/4.76  thf(t174_relat_1, axiom,
% 4.55/4.76    (![A:$i,B:$i]:
% 4.55/4.76     ( ( v1_relat_1 @ B ) =>
% 4.55/4.76       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 4.55/4.76            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 4.55/4.76            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 4.55/4.76  thf('16', plain,
% 4.55/4.76      (![X13 : $i, X14 : $i]:
% 4.55/4.76         (((X13) = (k1_xboole_0))
% 4.55/4.76          | ~ (v1_relat_1 @ X14)
% 4.55/4.76          | ~ (r1_tarski @ X13 @ (k2_relat_1 @ X14))
% 4.55/4.76          | ((k10_relat_1 @ X14 @ X13) != (k1_xboole_0)))),
% 4.55/4.76      inference('cnf', [status(esa)], [t174_relat_1])).
% 4.55/4.76  thf('17', plain,
% 4.55/4.76      (![X0 : $i]:
% 4.55/4.76         (((k10_relat_1 @ sk_B @ (k6_subset_1 @ sk_A @ X0)) != (k1_xboole_0))
% 4.55/4.76          | ~ (v1_relat_1 @ sk_B)
% 4.55/4.76          | ((k6_subset_1 @ sk_A @ X0) = (k1_xboole_0)))),
% 4.55/4.76      inference('sup-', [status(thm)], ['15', '16'])).
% 4.55/4.76  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 4.55/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.76  thf('19', plain,
% 4.55/4.76      (![X0 : $i]:
% 4.55/4.76         (((k10_relat_1 @ sk_B @ (k6_subset_1 @ sk_A @ X0)) != (k1_xboole_0))
% 4.55/4.76          | ((k6_subset_1 @ sk_A @ X0) = (k1_xboole_0)))),
% 4.55/4.76      inference('demod', [status(thm)], ['17', '18'])).
% 4.55/4.76  thf('20', plain,
% 4.55/4.76      ((((k1_xboole_0) != (k1_xboole_0))
% 4.55/4.76        | ~ (v1_relat_1 @ sk_B)
% 4.55/4.76        | ~ (v1_funct_1 @ sk_B)
% 4.55/4.76        | ((k6_subset_1 @ sk_A @ 
% 4.55/4.76            (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))) = (k1_xboole_0)))),
% 4.55/4.76      inference('sup-', [status(thm)], ['10', '19'])).
% 4.55/4.76  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 4.55/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.76  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 4.55/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.76  thf('23', plain,
% 4.55/4.76      ((((k1_xboole_0) != (k1_xboole_0))
% 4.55/4.76        | ((k6_subset_1 @ sk_A @ 
% 4.55/4.76            (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))) = (k1_xboole_0)))),
% 4.55/4.76      inference('demod', [status(thm)], ['20', '21', '22'])).
% 4.55/4.76  thf('24', plain,
% 4.55/4.76      (((k6_subset_1 @ sk_A @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))
% 4.55/4.76         = (k1_xboole_0))),
% 4.55/4.76      inference('simplify', [status(thm)], ['23'])).
% 4.55/4.76  thf('25', plain,
% 4.55/4.76      (![X3 : $i, X4 : $i]:
% 4.55/4.76         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 4.55/4.76      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.55/4.76  thf('26', plain,
% 4.55/4.76      (![X9 : $i, X10 : $i]:
% 4.55/4.76         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 4.55/4.76      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.55/4.76  thf('27', plain,
% 4.55/4.76      (![X3 : $i, X4 : $i]:
% 4.55/4.76         ((r1_tarski @ X3 @ X4) | ((k6_subset_1 @ X3 @ X4) != (k1_xboole_0)))),
% 4.55/4.76      inference('demod', [status(thm)], ['25', '26'])).
% 4.55/4.76  thf('28', plain,
% 4.55/4.76      ((((k1_xboole_0) != (k1_xboole_0))
% 4.55/4.76        | (r1_tarski @ sk_A @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 4.55/4.76      inference('sup-', [status(thm)], ['24', '27'])).
% 4.55/4.76  thf('29', plain,
% 4.55/4.76      ((r1_tarski @ sk_A @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))),
% 4.55/4.76      inference('simplify', [status(thm)], ['28'])).
% 4.55/4.76  thf(t145_funct_1, axiom,
% 4.55/4.76    (![A:$i,B:$i]:
% 4.55/4.76     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.55/4.76       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 4.55/4.76  thf('30', plain,
% 4.55/4.76      (![X18 : $i, X19 : $i]:
% 4.55/4.76         ((r1_tarski @ (k9_relat_1 @ X18 @ (k10_relat_1 @ X18 @ X19)) @ X19)
% 4.55/4.76          | ~ (v1_funct_1 @ X18)
% 4.55/4.76          | ~ (v1_relat_1 @ X18))),
% 4.55/4.76      inference('cnf', [status(esa)], [t145_funct_1])).
% 4.55/4.76  thf(d10_xboole_0, axiom,
% 4.55/4.76    (![A:$i,B:$i]:
% 4.55/4.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.55/4.76  thf('31', plain,
% 4.55/4.76      (![X0 : $i, X2 : $i]:
% 4.55/4.76         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.55/4.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.55/4.76  thf('32', plain,
% 4.55/4.76      (![X0 : $i, X1 : $i]:
% 4.55/4.76         (~ (v1_relat_1 @ X1)
% 4.55/4.76          | ~ (v1_funct_1 @ X1)
% 4.55/4.76          | ~ (r1_tarski @ X0 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)))
% 4.55/4.76          | ((X0) = (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))))),
% 4.55/4.76      inference('sup-', [status(thm)], ['30', '31'])).
% 4.55/4.76  thf('33', plain,
% 4.55/4.76      ((((sk_A) = (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))
% 4.55/4.76        | ~ (v1_funct_1 @ sk_B)
% 4.55/4.76        | ~ (v1_relat_1 @ sk_B))),
% 4.55/4.76      inference('sup-', [status(thm)], ['29', '32'])).
% 4.55/4.76  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 4.55/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.76  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 4.55/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.76  thf('36', plain,
% 4.55/4.76      (((sk_A) = (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))),
% 4.55/4.76      inference('demod', [status(thm)], ['33', '34', '35'])).
% 4.55/4.76  thf('37', plain,
% 4.55/4.76      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 4.55/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.76  thf('38', plain, ($false),
% 4.55/4.76      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 4.55/4.76  
% 4.55/4.76  % SZS output end Refutation
% 4.55/4.76  
% 4.55/4.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
