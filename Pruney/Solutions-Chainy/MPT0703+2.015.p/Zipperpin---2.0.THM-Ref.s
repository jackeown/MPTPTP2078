%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EaC7dTJxav

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:50 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 136 expanded)
%              Number of leaves         :   22 (  51 expanded)
%              Depth                    :   16
%              Number of atoms          :  567 (1241 expanded)
%              Number of equality atoms :   37 (  57 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t158_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ X15 @ ( k6_subset_1 @ X16 @ X17 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X15 @ X16 ) @ ( k10_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('7',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X6 @ ( k2_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k2_relat_1 @ X19 ) )
      | ( ( k9_relat_1 @ X19 @ ( k10_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
        = ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
      = ( k6_subset_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['10','22'])).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ X15 @ ( k6_subset_1 @ X16 @ X17 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X15 @ X16 ) @ ( k10_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ X15 @ ( k6_subset_1 @ X16 @ X17 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X15 @ X16 ) @ ( k10_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('30',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X6 @ ( k2_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ sk_A ) @ X0 ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['28','38'])).

thf('40',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('41',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ k1_xboole_0 @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['24','41'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('43',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('44',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['42','45','46','47'])).

thf('49',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k2_relat_1 @ X19 ) )
      | ( ( k9_relat_1 @ X19 @ ( k10_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( k1_xboole_0
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','55'])).

thf('57',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('59',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k6_subset_1 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EaC7dTJxav
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:11:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 240 iterations in 0.148s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.46/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.65  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(t158_funct_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.65       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.46/0.65           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.46/0.65         ( r1_tarski @ A @ B ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.65        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.65          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.46/0.65              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.46/0.65            ( r1_tarski @ A @ B ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.46/0.65  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(l32_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X3 : $i, X5 : $i]:
% 0.46/0.65         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.46/0.65      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.65  thf(redefinition_k6_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (![X13 : $i, X14 : $i]:
% 0.46/0.65         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (![X3 : $i, X5 : $i]:
% 0.46/0.65         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.46/0.65      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (((k6_subset_1 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.46/0.65         (k10_relat_1 @ sk_C @ sk_B)) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '4'])).
% 0.46/0.65  thf(t138_funct_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.65       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.46/0.65         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.65         (((k10_relat_1 @ X15 @ (k6_subset_1 @ X16 @ X17))
% 0.46/0.65            = (k6_subset_1 @ (k10_relat_1 @ X15 @ X16) @ 
% 0.46/0.65               (k10_relat_1 @ X15 @ X17)))
% 0.46/0.65          | ~ (v1_funct_1 @ X15)
% 0.46/0.65          | ~ (v1_relat_1 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      ((((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.46/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.65        | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.65      inference('sup+', [status(thm)], ['5', '6'])).
% 0.46/0.65  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.46/0.65  thf('11', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t10_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ X6 @ (k2_xboole_0 @ X8 @ X7)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.65  thf(t43_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.46/0.65       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.65         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.46/0.65          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X13 : $i, X14 : $i]:
% 0.46/0.65         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.65         ((r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X12)
% 0.46/0.65          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.46/0.65      inference('demod', [status(thm)], ['14', '15'])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['13', '16'])).
% 0.46/0.65  thf(t147_funct_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.65       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.46/0.65         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X18 : $i, X19 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X18 @ (k2_relat_1 @ X19))
% 0.46/0.65          | ((k9_relat_1 @ X19 @ (k10_relat_1 @ X19 @ X18)) = (X18))
% 0.46/0.65          | ~ (v1_funct_1 @ X19)
% 0.46/0.65          | ~ (v1_relat_1 @ X19))),
% 0.46/0.65      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ sk_C)
% 0.46/0.65          | ~ (v1_funct_1 @ sk_C)
% 0.46/0.65          | ((k9_relat_1 @ sk_C @ 
% 0.46/0.65              (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.46/0.65              = (k6_subset_1 @ sk_A @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.65  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.46/0.65           = (k6_subset_1 @ sk_A @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (((k9_relat_1 @ sk_C @ k1_xboole_0) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.46/0.65      inference('sup+', [status(thm)], ['10', '22'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.65         (((k10_relat_1 @ X15 @ (k6_subset_1 @ X16 @ X17))
% 0.46/0.65            = (k6_subset_1 @ (k10_relat_1 @ X15 @ X16) @ 
% 0.46/0.65               (k10_relat_1 @ X15 @ X17)))
% 0.46/0.65          | ~ (v1_funct_1 @ X15)
% 0.46/0.65          | ~ (v1_relat_1 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.46/0.65  thf(d10_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.65  thf('26', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.65      inference('simplify', [status(thm)], ['25'])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X3 : $i, X5 : $i]:
% 0.46/0.65         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.46/0.65      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.65  thf('28', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.65         (((k10_relat_1 @ X15 @ (k6_subset_1 @ X16 @ X17))
% 0.46/0.65            = (k6_subset_1 @ (k10_relat_1 @ X15 @ X16) @ 
% 0.46/0.65               (k10_relat_1 @ X15 @ X17)))
% 0.46/0.65          | ~ (v1_funct_1 @ X15)
% 0.46/0.65          | ~ (v1_relat_1 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ X6 @ (k2_xboole_0 @ X8 @ X7)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.46/0.65          (k2_xboole_0 @ X0 @ (k10_relat_1 @ sk_C @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.65         ((r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X12)
% 0.46/0.65          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.46/0.65      inference('demod', [status(thm)], ['14', '15'])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (r1_tarski @ (k6_subset_1 @ (k10_relat_1 @ sk_C @ sk_A) @ X0) @ 
% 0.46/0.65          (k10_relat_1 @ sk_C @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r1_tarski @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)) @ 
% 0.46/0.65           (k10_relat_1 @ sk_C @ sk_B))
% 0.46/0.65          | ~ (v1_relat_1 @ sk_C)
% 0.46/0.65          | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.65      inference('sup+', [status(thm)], ['29', '34'])).
% 0.46/0.65  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (r1_tarski @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)) @ 
% 0.46/0.65          (k10_relat_1 @ sk_C @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      ((r1_tarski @ (k10_relat_1 @ sk_C @ k1_xboole_0) @ 
% 0.46/0.65        (k10_relat_1 @ sk_C @ sk_B))),
% 0.46/0.65      inference('sup+', [status(thm)], ['28', '38'])).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (![X3 : $i, X5 : $i]:
% 0.46/0.65         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.46/0.65      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (((k6_subset_1 @ (k10_relat_1 @ sk_C @ k1_xboole_0) @ 
% 0.46/0.65         (k10_relat_1 @ sk_C @ sk_B)) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      ((((k10_relat_1 @ sk_C @ (k6_subset_1 @ k1_xboole_0 @ sk_B))
% 0.46/0.65          = (k1_xboole_0))
% 0.46/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.65        | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.65      inference('sup+', [status(thm)], ['24', '41'])).
% 0.46/0.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.65  thf('43', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (![X3 : $i, X5 : $i]:
% 0.46/0.65         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.46/0.65      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.65  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('48', plain, (((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['42', '45', '46', '47'])).
% 0.46/0.65  thf('49', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      (![X18 : $i, X19 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X18 @ (k2_relat_1 @ X19))
% 0.46/0.65          | ((k9_relat_1 @ X19 @ (k10_relat_1 @ X19 @ X18)) = (X18))
% 0.46/0.65          | ~ (v1_funct_1 @ X19)
% 0.46/0.65          | ~ (v1_relat_1 @ X19))),
% 0.46/0.65      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 0.46/0.65              = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      ((((k9_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.65        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.65      inference('sup+', [status(thm)], ['48', '51'])).
% 0.46/0.65  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('55', plain, (((k9_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.46/0.65  thf('56', plain, (((k1_xboole_0) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['23', '55'])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      (![X3 : $i, X4 : $i]:
% 0.46/0.65         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      (![X13 : $i, X14 : $i]:
% 0.46/0.65         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      (![X3 : $i, X4 : $i]:
% 0.46/0.65         ((r1_tarski @ X3 @ X4) | ((k6_subset_1 @ X3 @ X4) != (k1_xboole_0)))),
% 0.46/0.65      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['56', '59'])).
% 0.46/0.65  thf('61', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.46/0.65      inference('simplify', [status(thm)], ['60'])).
% 0.46/0.65  thf('62', plain, ($false), inference('demod', [status(thm)], ['0', '61'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
