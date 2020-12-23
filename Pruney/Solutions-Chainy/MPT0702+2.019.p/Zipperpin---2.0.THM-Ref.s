%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n0b07IdHG7

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:44 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   76 (  97 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  488 ( 870 expanded)
%              Number of equality atoms :   29 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t157_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( v2_funct_1 @ C ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k10_relat_1 @ X23 @ X24 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X23 ) @ X24 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(t149_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X16: $i] :
      ( ( ( k9_relat_1 @ X16 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t149_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k6_subset_1 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t123_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
          = ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k9_relat_1 @ X18 @ ( k6_subset_1 @ X19 @ X20 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X18 @ X19 ) @ ( k9_relat_1 @ X18 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf('13',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X12 @ X13 ) @ X12 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k6_subset_1 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( r1_tarski @ X21 @ ( k10_relat_1 @ X22 @ ( k9_relat_1 @ X22 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['6','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('37',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k6_subset_1 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['0','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n0b07IdHG7
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:23:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.90/1.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.09  % Solved by: fo/fo7.sh
% 0.90/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.09  % done 1182 iterations in 0.609s
% 0.90/1.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.09  % SZS output start Refutation
% 0.90/1.09  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.09  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.09  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.90/1.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.09  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.09  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.90/1.09  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.90/1.09  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.09  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.90/1.09  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.09  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.09  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.90/1.09  thf(t157_funct_1, conjecture,
% 0.90/1.09    (![A:$i,B:$i,C:$i]:
% 0.90/1.09     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.90/1.09       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.90/1.09           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.90/1.09         ( r1_tarski @ A @ B ) ) ))).
% 0.90/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.09    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.09        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.90/1.09          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.90/1.09              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.90/1.09            ( r1_tarski @ A @ B ) ) ) )),
% 0.90/1.09    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.90/1.09  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(dt_k2_funct_1, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.09       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.90/1.09         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.90/1.09  thf('1', plain,
% 0.90/1.09      (![X17 : $i]:
% 0.90/1.09         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 0.90/1.09          | ~ (v1_funct_1 @ X17)
% 0.90/1.09          | ~ (v1_relat_1 @ X17))),
% 0.90/1.09      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.90/1.09  thf(t155_funct_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.09       ( ( v2_funct_1 @ B ) =>
% 0.90/1.09         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.90/1.09  thf('2', plain,
% 0.90/1.09      (![X23 : $i, X24 : $i]:
% 0.90/1.09         (~ (v2_funct_1 @ X23)
% 0.90/1.09          | ((k10_relat_1 @ X23 @ X24)
% 0.90/1.09              = (k9_relat_1 @ (k2_funct_1 @ X23) @ X24))
% 0.90/1.09          | ~ (v1_funct_1 @ X23)
% 0.90/1.09          | ~ (v1_relat_1 @ X23))),
% 0.90/1.09      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.90/1.09  thf(t149_relat_1, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( v1_relat_1 @ A ) =>
% 0.90/1.09       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.90/1.09  thf('3', plain,
% 0.90/1.09      (![X16 : $i]:
% 0.90/1.09         (((k9_relat_1 @ X16 @ k1_xboole_0) = (k1_xboole_0))
% 0.90/1.09          | ~ (v1_relat_1 @ X16))),
% 0.90/1.09      inference('cnf', [status(esa)], [t149_relat_1])).
% 0.90/1.09  thf('4', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (((k10_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.90/1.09          | ~ (v1_relat_1 @ X0)
% 0.90/1.09          | ~ (v1_funct_1 @ X0)
% 0.90/1.09          | ~ (v2_funct_1 @ X0)
% 0.90/1.09          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.90/1.09      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.09  thf('5', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X0)
% 0.90/1.09          | ~ (v1_funct_1 @ X0)
% 0.90/1.09          | ~ (v2_funct_1 @ X0)
% 0.90/1.09          | ~ (v1_funct_1 @ X0)
% 0.90/1.09          | ~ (v1_relat_1 @ X0)
% 0.90/1.09          | ((k10_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['1', '4'])).
% 0.90/1.09  thf('6', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (((k10_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.90/1.09          | ~ (v2_funct_1 @ X0)
% 0.90/1.09          | ~ (v1_funct_1 @ X0)
% 0.90/1.09          | ~ (v1_relat_1 @ X0))),
% 0.90/1.09      inference('simplify', [status(thm)], ['5'])).
% 0.90/1.09  thf('7', plain,
% 0.90/1.09      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(l32_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.09  thf('8', plain,
% 0.90/1.09      (![X3 : $i, X5 : $i]:
% 0.90/1.09         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.90/1.09      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.90/1.09  thf(redefinition_k6_subset_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.90/1.09  thf('9', plain,
% 0.90/1.09      (![X14 : $i, X15 : $i]:
% 0.90/1.09         ((k6_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))),
% 0.90/1.09      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.90/1.09  thf('10', plain,
% 0.90/1.09      (![X3 : $i, X5 : $i]:
% 0.90/1.09         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.90/1.09      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.09  thf('11', plain,
% 0.90/1.09      (((k6_subset_1 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))
% 0.90/1.09         = (k1_xboole_0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['7', '10'])).
% 0.90/1.09  thf(t123_funct_1, axiom,
% 0.90/1.09    (![A:$i,B:$i,C:$i]:
% 0.90/1.09     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.90/1.09       ( ( v2_funct_1 @ C ) =>
% 0.90/1.09         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.90/1.09           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.90/1.09  thf('12', plain,
% 0.90/1.09      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.90/1.09         (~ (v2_funct_1 @ X18)
% 0.90/1.09          | ((k9_relat_1 @ X18 @ (k6_subset_1 @ X19 @ X20))
% 0.90/1.09              = (k6_subset_1 @ (k9_relat_1 @ X18 @ X19) @ 
% 0.90/1.09                 (k9_relat_1 @ X18 @ X20)))
% 0.90/1.09          | ~ (v1_funct_1 @ X18)
% 0.90/1.09          | ~ (v1_relat_1 @ X18))),
% 0.90/1.09      inference('cnf', [status(esa)], [t123_funct_1])).
% 0.90/1.09  thf('13', plain,
% 0.90/1.09      ((((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.90/1.09        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.09        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.09        | ~ (v2_funct_1 @ sk_C))),
% 0.90/1.09      inference('sup+', [status(thm)], ['11', '12'])).
% 0.90/1.09  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('16', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('17', plain,
% 0.90/1.09      (((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.90/1.09      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.90/1.09  thf('18', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(t36_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.90/1.09  thf('19', plain,
% 0.90/1.09      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.90/1.09      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.90/1.09  thf('20', plain,
% 0.90/1.09      (![X14 : $i, X15 : $i]:
% 0.90/1.09         ((k6_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))),
% 0.90/1.09      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.90/1.09  thf('21', plain,
% 0.90/1.09      (![X12 : $i, X13 : $i]: (r1_tarski @ (k6_subset_1 @ X12 @ X13) @ X12)),
% 0.90/1.09      inference('demod', [status(thm)], ['19', '20'])).
% 0.90/1.09  thf(t12_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.90/1.09  thf('22', plain,
% 0.90/1.09      (![X9 : $i, X10 : $i]:
% 0.90/1.09         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.90/1.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.90/1.09  thf('23', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X0) = (X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.09  thf(t11_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i,C:$i]:
% 0.90/1.09     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.90/1.09  thf('24', plain,
% 0.90/1.09      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.90/1.09         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 0.90/1.09      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.90/1.09  thf('25', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.09         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k6_subset_1 @ X0 @ X2) @ X1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.09  thf('26', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k1_relat_1 @ sk_C))),
% 0.90/1.09      inference('sup-', [status(thm)], ['18', '25'])).
% 0.90/1.09  thf(t146_funct_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( v1_relat_1 @ B ) =>
% 0.90/1.09       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.90/1.09         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.90/1.09  thf('27', plain,
% 0.90/1.09      (![X21 : $i, X22 : $i]:
% 0.90/1.09         (~ (r1_tarski @ X21 @ (k1_relat_1 @ X22))
% 0.90/1.09          | (r1_tarski @ X21 @ (k10_relat_1 @ X22 @ (k9_relat_1 @ X22 @ X21)))
% 0.90/1.09          | ~ (v1_relat_1 @ X22))),
% 0.90/1.09      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.90/1.09  thf('28', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ sk_C)
% 0.90/1.09          | (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ 
% 0.90/1.09             (k10_relat_1 @ sk_C @ 
% 0.90/1.09              (k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['26', '27'])).
% 0.90/1.09  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('30', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ 
% 0.90/1.09          (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0))))),
% 0.90/1.09      inference('demod', [status(thm)], ['28', '29'])).
% 0.90/1.09  thf('31', plain,
% 0.90/1.09      ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ 
% 0.90/1.09        (k10_relat_1 @ sk_C @ k1_xboole_0))),
% 0.90/1.09      inference('sup+', [status(thm)], ['17', '30'])).
% 0.90/1.09  thf('32', plain,
% 0.90/1.09      (((r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.90/1.09        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.09        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.09        | ~ (v2_funct_1 @ sk_C))),
% 0.90/1.09      inference('sup+', [status(thm)], ['6', '31'])).
% 0.90/1.09  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('35', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('36', plain, ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ k1_xboole_0)),
% 0.90/1.09      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.90/1.09  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.90/1.09  thf('37', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.90/1.09      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.90/1.09  thf(d10_xboole_0, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.09  thf('38', plain,
% 0.90/1.09      (![X0 : $i, X2 : $i]:
% 0.90/1.09         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.09  thf('39', plain,
% 0.90/1.09      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.09  thf('40', plain, (((k6_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['36', '39'])).
% 0.90/1.09  thf('41', plain,
% 0.90/1.09      (![X3 : $i, X4 : $i]:
% 0.90/1.09         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.90/1.09      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.90/1.09  thf('42', plain,
% 0.90/1.09      (![X14 : $i, X15 : $i]:
% 0.90/1.09         ((k6_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))),
% 0.90/1.09      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.90/1.09  thf('43', plain,
% 0.90/1.09      (![X3 : $i, X4 : $i]:
% 0.90/1.09         ((r1_tarski @ X3 @ X4) | ((k6_subset_1 @ X3 @ X4) != (k1_xboole_0)))),
% 0.90/1.09      inference('demod', [status(thm)], ['41', '42'])).
% 0.90/1.09  thf('44', plain,
% 0.90/1.09      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.90/1.09      inference('sup-', [status(thm)], ['40', '43'])).
% 0.90/1.09  thf('45', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.90/1.09      inference('simplify', [status(thm)], ['44'])).
% 0.90/1.09  thf('46', plain, ($false), inference('demod', [status(thm)], ['0', '45'])).
% 0.90/1.09  
% 0.90/1.09  % SZS output end Refutation
% 0.90/1.09  
% 0.90/1.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
