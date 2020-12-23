%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qy0KxMyIpa

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:30 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   73 (  96 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   18
%              Number of atoms          :  525 ( 847 expanded)
%              Number of equality atoms :   34 (  57 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('0',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X22 @ ( k10_relat_1 @ X22 @ X23 ) ) @ X23 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k10_relat_1 @ X19 @ ( k6_subset_1 @ X20 @ X21 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X19 @ X20 ) @ ( k10_relat_1 @ X19 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X13: $i] :
      ( ( ( k10_relat_1 @ X13 @ ( k2_relat_1 @ X13 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

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

thf('3',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( r1_tarski @ ( k10_relat_1 @ X18 @ X16 ) @ ( k10_relat_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X24 @ ( k1_relat_1 @ X25 ) )
      | ( r1_tarski @ X24 @ ( k10_relat_1 @ X25 @ ( k9_relat_1 @ X25 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X9 @ X10 ) @ X9 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf(t174_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( r1_tarski @ X14 @ ( k2_relat_1 @ X15 ) )
      | ( ( k10_relat_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t174_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k6_subset_1 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
       != k1_xboole_0 )
      | ( ( k6_subset_1 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,
    ( ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k6_subset_1 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    r1_tarski @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['44','45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qy0KxMyIpa
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:29:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.61  % Solved by: fo/fo7.sh
% 0.36/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.61  % done 328 iterations in 0.155s
% 0.36/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.61  % SZS output start Refutation
% 0.36/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.61  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.36/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.61  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.36/0.61  thf(t145_funct_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.61       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.36/0.61  thf('0', plain,
% 0.36/0.61      (![X22 : $i, X23 : $i]:
% 0.36/0.61         ((r1_tarski @ (k9_relat_1 @ X22 @ (k10_relat_1 @ X22 @ X23)) @ X23)
% 0.36/0.61          | ~ (v1_funct_1 @ X22)
% 0.36/0.61          | ~ (v1_relat_1 @ X22))),
% 0.36/0.61      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.36/0.61  thf(t138_funct_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.61       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.36/0.61         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.36/0.61  thf('1', plain,
% 0.36/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.36/0.61         (((k10_relat_1 @ X19 @ (k6_subset_1 @ X20 @ X21))
% 0.36/0.61            = (k6_subset_1 @ (k10_relat_1 @ X19 @ X20) @ 
% 0.36/0.61               (k10_relat_1 @ X19 @ X21)))
% 0.36/0.61          | ~ (v1_funct_1 @ X19)
% 0.36/0.61          | ~ (v1_relat_1 @ X19))),
% 0.36/0.61      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.36/0.61  thf(t169_relat_1, axiom,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( v1_relat_1 @ A ) =>
% 0.36/0.61       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.36/0.61  thf('2', plain,
% 0.36/0.61      (![X13 : $i]:
% 0.36/0.61         (((k10_relat_1 @ X13 @ (k2_relat_1 @ X13)) = (k1_relat_1 @ X13))
% 0.36/0.61          | ~ (v1_relat_1 @ X13))),
% 0.36/0.61      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.36/0.61  thf(t147_funct_1, conjecture,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.61       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.36/0.61         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.36/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.61    (~( ![A:$i,B:$i]:
% 0.36/0.61        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.61          ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.36/0.61            ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.36/0.61    inference('cnf.neg', [status(esa)], [t147_funct_1])).
% 0.36/0.61  thf('3', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(t178_relat_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( v1_relat_1 @ C ) =>
% 0.36/0.61       ( ( r1_tarski @ A @ B ) =>
% 0.36/0.61         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.36/0.61  thf('4', plain,
% 0.36/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.61         (~ (r1_tarski @ X16 @ X17)
% 0.36/0.61          | ~ (v1_relat_1 @ X18)
% 0.36/0.61          | (r1_tarski @ (k10_relat_1 @ X18 @ X16) @ (k10_relat_1 @ X18 @ X17)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.36/0.61  thf('5', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ 
% 0.36/0.61           (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B)))
% 0.36/0.61          | ~ (v1_relat_1 @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.61  thf('6', plain,
% 0.36/0.61      (((r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.36/0.61        | ~ (v1_relat_1 @ sk_B)
% 0.36/0.61        | ~ (v1_relat_1 @ sk_B))),
% 0.36/0.61      inference('sup+', [status(thm)], ['2', '5'])).
% 0.36/0.61  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('9', plain,
% 0.36/0.61      ((r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.36/0.61      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.36/0.61  thf(t146_funct_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( v1_relat_1 @ B ) =>
% 0.36/0.61       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.36/0.61         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.36/0.61  thf('10', plain,
% 0.36/0.61      (![X24 : $i, X25 : $i]:
% 0.36/0.61         (~ (r1_tarski @ X24 @ (k1_relat_1 @ X25))
% 0.36/0.61          | (r1_tarski @ X24 @ (k10_relat_1 @ X25 @ (k9_relat_1 @ X25 @ X24)))
% 0.36/0.61          | ~ (v1_relat_1 @ X25))),
% 0.36/0.61      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.36/0.61  thf('11', plain,
% 0.36/0.61      ((~ (v1_relat_1 @ sk_B)
% 0.36/0.61        | (r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ 
% 0.36/0.61           (k10_relat_1 @ sk_B @ 
% 0.36/0.61            (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))))),
% 0.36/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.61  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('13', plain,
% 0.36/0.61      ((r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ 
% 0.36/0.61        (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 0.36/0.61      inference('demod', [status(thm)], ['11', '12'])).
% 0.36/0.61  thf(l32_xboole_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.61  thf('14', plain,
% 0.36/0.61      (![X3 : $i, X5 : $i]:
% 0.36/0.61         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.36/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.61  thf(redefinition_k6_subset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.36/0.61  thf('15', plain,
% 0.36/0.61      (![X11 : $i, X12 : $i]:
% 0.36/0.61         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.36/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.36/0.61  thf('16', plain,
% 0.36/0.61      (![X3 : $i, X5 : $i]:
% 0.36/0.61         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.36/0.61      inference('demod', [status(thm)], ['14', '15'])).
% 0.36/0.61  thf('17', plain,
% 0.36/0.61      (((k6_subset_1 @ (k10_relat_1 @ sk_B @ sk_A) @ 
% 0.36/0.61         (k10_relat_1 @ sk_B @ 
% 0.36/0.61          (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))
% 0.36/0.61         = (k1_xboole_0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['13', '16'])).
% 0.36/0.61  thf('18', plain,
% 0.36/0.61      ((((k10_relat_1 @ sk_B @ 
% 0.36/0.61          (k6_subset_1 @ sk_A @ 
% 0.36/0.61           (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))
% 0.36/0.61          = (k1_xboole_0))
% 0.36/0.61        | ~ (v1_relat_1 @ sk_B)
% 0.36/0.61        | ~ (v1_funct_1 @ sk_B))),
% 0.36/0.61      inference('sup+', [status(thm)], ['1', '17'])).
% 0.36/0.61  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('20', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('21', plain,
% 0.36/0.61      (((k10_relat_1 @ sk_B @ 
% 0.36/0.61         (k6_subset_1 @ sk_A @ 
% 0.36/0.61          (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))
% 0.36/0.61         = (k1_xboole_0))),
% 0.36/0.61      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.36/0.61  thf('22', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(t36_xboole_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.61  thf('23', plain,
% 0.36/0.61      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.36/0.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.61  thf('24', plain,
% 0.36/0.61      (![X11 : $i, X12 : $i]:
% 0.36/0.61         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.36/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.36/0.61  thf('25', plain,
% 0.36/0.61      (![X9 : $i, X10 : $i]: (r1_tarski @ (k6_subset_1 @ X9 @ X10) @ X9)),
% 0.36/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.61  thf(t1_xboole_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.36/0.61       ( r1_tarski @ A @ C ) ))).
% 0.36/0.61  thf('26', plain,
% 0.36/0.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.61         (~ (r1_tarski @ X6 @ X7)
% 0.36/0.61          | ~ (r1_tarski @ X7 @ X8)
% 0.36/0.61          | (r1_tarski @ X6 @ X8))),
% 0.36/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.36/0.61  thf('27', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.61         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.61  thf('28', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_B))),
% 0.36/0.61      inference('sup-', [status(thm)], ['22', '27'])).
% 0.36/0.61  thf(t174_relat_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( v1_relat_1 @ B ) =>
% 0.36/0.61       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.61            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.36/0.61            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.36/0.61  thf('29', plain,
% 0.36/0.61      (![X14 : $i, X15 : $i]:
% 0.36/0.61         (((X14) = (k1_xboole_0))
% 0.36/0.61          | ~ (v1_relat_1 @ X15)
% 0.36/0.61          | ~ (r1_tarski @ X14 @ (k2_relat_1 @ X15))
% 0.36/0.61          | ((k10_relat_1 @ X15 @ X14) != (k1_xboole_0)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t174_relat_1])).
% 0.36/0.61  thf('30', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         (((k10_relat_1 @ sk_B @ (k6_subset_1 @ sk_A @ X0)) != (k1_xboole_0))
% 0.36/0.61          | ~ (v1_relat_1 @ sk_B)
% 0.36/0.61          | ((k6_subset_1 @ sk_A @ X0) = (k1_xboole_0)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.61  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('32', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         (((k10_relat_1 @ sk_B @ (k6_subset_1 @ sk_A @ X0)) != (k1_xboole_0))
% 0.36/0.61          | ((k6_subset_1 @ sk_A @ X0) = (k1_xboole_0)))),
% 0.36/0.61      inference('demod', [status(thm)], ['30', '31'])).
% 0.36/0.61  thf('33', plain,
% 0.36/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.61        | ((k6_subset_1 @ sk_A @ 
% 0.36/0.61            (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))) = (k1_xboole_0)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['21', '32'])).
% 0.36/0.61  thf('34', plain,
% 0.36/0.61      (((k6_subset_1 @ sk_A @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))
% 0.36/0.61         = (k1_xboole_0))),
% 0.36/0.61      inference('simplify', [status(thm)], ['33'])).
% 0.36/0.61  thf('35', plain,
% 0.36/0.61      (![X3 : $i, X4 : $i]:
% 0.36/0.61         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.36/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.61  thf('36', plain,
% 0.36/0.61      (![X11 : $i, X12 : $i]:
% 0.36/0.61         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.36/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.36/0.61  thf('37', plain,
% 0.36/0.61      (![X3 : $i, X4 : $i]:
% 0.36/0.61         ((r1_tarski @ X3 @ X4) | ((k6_subset_1 @ X3 @ X4) != (k1_xboole_0)))),
% 0.36/0.61      inference('demod', [status(thm)], ['35', '36'])).
% 0.36/0.61  thf('38', plain,
% 0.36/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.61        | (r1_tarski @ sk_A @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 0.36/0.61      inference('sup-', [status(thm)], ['34', '37'])).
% 0.36/0.61  thf('39', plain,
% 0.36/0.61      ((r1_tarski @ sk_A @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))),
% 0.36/0.61      inference('simplify', [status(thm)], ['38'])).
% 0.36/0.61  thf(d10_xboole_0, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.61  thf('40', plain,
% 0.36/0.61      (![X0 : $i, X2 : $i]:
% 0.36/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.61  thf('41', plain,
% 0.36/0.61      ((~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)) @ sk_A)
% 0.36/0.61        | ((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.61  thf('42', plain,
% 0.36/0.61      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('43', plain,
% 0.36/0.61      (~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 0.36/0.61      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.36/0.61  thf('44', plain, ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B))),
% 0.36/0.61      inference('sup-', [status(thm)], ['0', '43'])).
% 0.36/0.61  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('47', plain, ($false),
% 0.36/0.61      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.36/0.61  
% 0.36/0.61  % SZS output end Refutation
% 0.36/0.61  
% 0.36/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
