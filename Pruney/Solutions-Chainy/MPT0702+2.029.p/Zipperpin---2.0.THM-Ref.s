%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hHrSMssZCH

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:46 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 152 expanded)
%              Number of leaves         :   25 (  57 expanded)
%              Depth                    :   16
%              Number of atoms          :  534 (1437 expanded)
%              Number of equality atoms :   34 (  58 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf(t123_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
          = ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k9_relat_1 @ X16 @ ( k6_subset_1 @ X17 @ X18 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X16 @ X17 ) @ ( k9_relat_1 @ X16 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf('2',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k6_subset_1 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X12 @ X13 ) @ X12 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k6_subset_1 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( r1_tarski @ X19 @ ( k10_relat_1 @ X20 @ ( k9_relat_1 @ X20 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k9_relat_1 @ X16 @ ( k6_subset_1 @ X17 @ X18 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X16 @ X17 ) @ ( k9_relat_1 @ X16 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ ( k6_subset_1 @ sk_A @ sk_B ) @ X0 ) )
        = ( k6_subset_1 @ k1_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X12 @ X13 ) @ X12 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('34',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ ( k6_subset_1 @ sk_A @ sk_B ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','37','38','39','40'])).

thf('42',plain,
    ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['29','41'])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('43',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( r1_tarski @ ( k10_relat_1 @ X21 @ ( k9_relat_1 @ X21 @ X22 ) ) @ X22 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('44',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('50',plain,
    ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['25','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('53',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('55',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('56',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k6_subset_1 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['0','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hHrSMssZCH
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.84  % Solved by: fo/fo7.sh
% 0.61/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.84  % done 420 iterations in 0.360s
% 0.61/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.84  % SZS output start Refutation
% 0.61/0.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.84  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.61/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.61/0.84  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.61/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.61/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.84  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.61/0.84  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.61/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.84  thf(t157_funct_1, conjecture,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.61/0.84       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.61/0.84           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.61/0.84         ( r1_tarski @ A @ B ) ) ))).
% 0.61/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.84    (~( ![A:$i,B:$i,C:$i]:
% 0.61/0.84        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.61/0.84          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.61/0.84              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.61/0.84            ( r1_tarski @ A @ B ) ) ) )),
% 0.61/0.84    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.61/0.84  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(t123_funct_1, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.61/0.84       ( ( v2_funct_1 @ C ) =>
% 0.61/0.84         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.61/0.84           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.61/0.84  thf('1', plain,
% 0.61/0.84      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.84         (~ (v2_funct_1 @ X16)
% 0.61/0.84          | ((k9_relat_1 @ X16 @ (k6_subset_1 @ X17 @ X18))
% 0.61/0.84              = (k6_subset_1 @ (k9_relat_1 @ X16 @ X17) @ 
% 0.61/0.84                 (k9_relat_1 @ X16 @ X18)))
% 0.61/0.84          | ~ (v1_funct_1 @ X16)
% 0.61/0.84          | ~ (v1_relat_1 @ X16))),
% 0.61/0.84      inference('cnf', [status(esa)], [t123_funct_1])).
% 0.61/0.84  thf('2', plain,
% 0.61/0.84      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(l32_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.61/0.84  thf('3', plain,
% 0.61/0.84      (![X3 : $i, X5 : $i]:
% 0.61/0.84         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.61/0.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.61/0.84  thf(redefinition_k6_subset_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.61/0.84  thf('4', plain,
% 0.61/0.84      (![X14 : $i, X15 : $i]:
% 0.61/0.84         ((k6_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))),
% 0.61/0.84      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.61/0.84  thf('5', plain,
% 0.61/0.84      (![X3 : $i, X5 : $i]:
% 0.61/0.84         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.61/0.84      inference('demod', [status(thm)], ['3', '4'])).
% 0.61/0.84  thf('6', plain,
% 0.61/0.84      (((k6_subset_1 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))
% 0.61/0.84         = (k1_xboole_0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['2', '5'])).
% 0.61/0.84  thf('7', plain,
% 0.61/0.84      ((((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.61/0.84        | ~ (v1_relat_1 @ sk_C)
% 0.61/0.84        | ~ (v1_funct_1 @ sk_C)
% 0.61/0.84        | ~ (v2_funct_1 @ sk_C))),
% 0.61/0.84      inference('sup+', [status(thm)], ['1', '6'])).
% 0.61/0.84  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('10', plain, ((v2_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('11', plain,
% 0.61/0.84      (((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.61/0.84      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.61/0.84  thf('12', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(t36_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.61/0.84  thf('13', plain,
% 0.61/0.84      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.61/0.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.61/0.84  thf('14', plain,
% 0.61/0.84      (![X14 : $i, X15 : $i]:
% 0.61/0.84         ((k6_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))),
% 0.61/0.84      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.61/0.84  thf('15', plain,
% 0.61/0.84      (![X12 : $i, X13 : $i]: (r1_tarski @ (k6_subset_1 @ X12 @ X13) @ X12)),
% 0.61/0.84      inference('demod', [status(thm)], ['13', '14'])).
% 0.61/0.84  thf(t12_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.61/0.84  thf('16', plain,
% 0.61/0.84      (![X9 : $i, X10 : $i]:
% 0.61/0.84         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.61/0.84      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.61/0.84  thf('17', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         ((k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X0) = (X0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['15', '16'])).
% 0.61/0.84  thf(t11_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.61/0.84  thf('18', plain,
% 0.61/0.84      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.61/0.84         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 0.61/0.84      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.61/0.84  thf('19', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.84         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k6_subset_1 @ X0 @ X2) @ X1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.84  thf('20', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k1_relat_1 @ sk_C))),
% 0.61/0.84      inference('sup-', [status(thm)], ['12', '19'])).
% 0.61/0.84  thf(t146_funct_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( v1_relat_1 @ B ) =>
% 0.61/0.84       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.61/0.84         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.61/0.84  thf('21', plain,
% 0.61/0.84      (![X19 : $i, X20 : $i]:
% 0.61/0.84         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 0.61/0.84          | (r1_tarski @ X19 @ (k10_relat_1 @ X20 @ (k9_relat_1 @ X20 @ X19)))
% 0.61/0.84          | ~ (v1_relat_1 @ X20))),
% 0.61/0.84      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.61/0.84  thf('22', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (~ (v1_relat_1 @ sk_C)
% 0.61/0.84          | (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ 
% 0.61/0.84             (k10_relat_1 @ sk_C @ 
% 0.61/0.84              (k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['20', '21'])).
% 0.61/0.84  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('24', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ 
% 0.61/0.84          (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0))))),
% 0.61/0.84      inference('demod', [status(thm)], ['22', '23'])).
% 0.61/0.84  thf('25', plain,
% 0.61/0.84      ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ 
% 0.61/0.84        (k10_relat_1 @ sk_C @ k1_xboole_0))),
% 0.61/0.84      inference('sup+', [status(thm)], ['11', '24'])).
% 0.61/0.84  thf(d10_xboole_0, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.84  thf('26', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.61/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.84  thf('27', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.61/0.84      inference('simplify', [status(thm)], ['26'])).
% 0.61/0.84  thf('28', plain,
% 0.61/0.84      (![X3 : $i, X5 : $i]:
% 0.61/0.84         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.61/0.84      inference('demod', [status(thm)], ['3', '4'])).
% 0.61/0.84  thf('29', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['27', '28'])).
% 0.61/0.84  thf('30', plain,
% 0.61/0.84      (((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.61/0.84      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.61/0.84  thf('31', plain,
% 0.61/0.84      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.84         (~ (v2_funct_1 @ X16)
% 0.61/0.84          | ((k9_relat_1 @ X16 @ (k6_subset_1 @ X17 @ X18))
% 0.61/0.84              = (k6_subset_1 @ (k9_relat_1 @ X16 @ X17) @ 
% 0.61/0.84                 (k9_relat_1 @ X16 @ X18)))
% 0.61/0.84          | ~ (v1_funct_1 @ X16)
% 0.61/0.84          | ~ (v1_relat_1 @ X16))),
% 0.61/0.84      inference('cnf', [status(esa)], [t123_funct_1])).
% 0.61/0.84  thf('32', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (((k9_relat_1 @ sk_C @ 
% 0.61/0.84            (k6_subset_1 @ (k6_subset_1 @ sk_A @ sk_B) @ X0))
% 0.61/0.84            = (k6_subset_1 @ k1_xboole_0 @ (k9_relat_1 @ sk_C @ X0)))
% 0.61/0.84          | ~ (v1_relat_1 @ sk_C)
% 0.61/0.84          | ~ (v1_funct_1 @ sk_C)
% 0.61/0.84          | ~ (v2_funct_1 @ sk_C))),
% 0.61/0.84      inference('sup+', [status(thm)], ['30', '31'])).
% 0.61/0.84  thf('33', plain,
% 0.61/0.84      (![X12 : $i, X13 : $i]: (r1_tarski @ (k6_subset_1 @ X12 @ X13) @ X12)),
% 0.61/0.84      inference('demod', [status(thm)], ['13', '14'])).
% 0.61/0.84  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.61/0.84  thf('34', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.61/0.84      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.61/0.84  thf('35', plain,
% 0.61/0.84      (![X0 : $i, X2 : $i]:
% 0.61/0.84         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.61/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.84  thf('36', plain,
% 0.61/0.84      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['34', '35'])).
% 0.61/0.84  thf('37', plain,
% 0.61/0.84      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['33', '36'])).
% 0.61/0.84  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('40', plain, ((v2_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('41', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         ((k9_relat_1 @ sk_C @ (k6_subset_1 @ (k6_subset_1 @ sk_A @ sk_B) @ X0))
% 0.61/0.84           = (k1_xboole_0))),
% 0.61/0.84      inference('demod', [status(thm)], ['32', '37', '38', '39', '40'])).
% 0.61/0.84  thf('42', plain, (((k9_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.84      inference('sup+', [status(thm)], ['29', '41'])).
% 0.61/0.84  thf(t152_funct_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.61/0.84       ( ( v2_funct_1 @ B ) =>
% 0.61/0.84         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.61/0.84  thf('43', plain,
% 0.61/0.84      (![X21 : $i, X22 : $i]:
% 0.61/0.84         (~ (v2_funct_1 @ X21)
% 0.61/0.84          | (r1_tarski @ (k10_relat_1 @ X21 @ (k9_relat_1 @ X21 @ X22)) @ X22)
% 0.61/0.84          | ~ (v1_funct_1 @ X21)
% 0.61/0.84          | ~ (v1_relat_1 @ X21))),
% 0.61/0.84      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.61/0.84  thf('44', plain,
% 0.61/0.84      (((r1_tarski @ (k10_relat_1 @ sk_C @ k1_xboole_0) @ k1_xboole_0)
% 0.61/0.84        | ~ (v1_relat_1 @ sk_C)
% 0.61/0.84        | ~ (v1_funct_1 @ sk_C)
% 0.61/0.84        | ~ (v2_funct_1 @ sk_C))),
% 0.61/0.84      inference('sup+', [status(thm)], ['42', '43'])).
% 0.61/0.84  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('48', plain,
% 0.61/0.84      ((r1_tarski @ (k10_relat_1 @ sk_C @ k1_xboole_0) @ k1_xboole_0)),
% 0.61/0.84      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.61/0.84  thf('49', plain,
% 0.61/0.84      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['34', '35'])).
% 0.61/0.84  thf('50', plain, (((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['48', '49'])).
% 0.61/0.84  thf('51', plain, ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ k1_xboole_0)),
% 0.61/0.84      inference('demod', [status(thm)], ['25', '50'])).
% 0.61/0.84  thf('52', plain,
% 0.61/0.84      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['34', '35'])).
% 0.61/0.84  thf('53', plain, (((k6_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['51', '52'])).
% 0.61/0.84  thf('54', plain,
% 0.61/0.84      (![X3 : $i, X4 : $i]:
% 0.61/0.84         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.61/0.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.61/0.84  thf('55', plain,
% 0.61/0.84      (![X14 : $i, X15 : $i]:
% 0.61/0.84         ((k6_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))),
% 0.61/0.84      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.61/0.84  thf('56', plain,
% 0.61/0.84      (![X3 : $i, X4 : $i]:
% 0.61/0.84         ((r1_tarski @ X3 @ X4) | ((k6_subset_1 @ X3 @ X4) != (k1_xboole_0)))),
% 0.61/0.84      inference('demod', [status(thm)], ['54', '55'])).
% 0.61/0.84  thf('57', plain,
% 0.61/0.84      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.61/0.84      inference('sup-', [status(thm)], ['53', '56'])).
% 0.61/0.84  thf('58', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.61/0.84      inference('simplify', [status(thm)], ['57'])).
% 0.61/0.84  thf('59', plain, ($false), inference('demod', [status(thm)], ['0', '58'])).
% 0.61/0.84  
% 0.61/0.84  % SZS output end Refutation
% 0.61/0.84  
% 0.61/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
