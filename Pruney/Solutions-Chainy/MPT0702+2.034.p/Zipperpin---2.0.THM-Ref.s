%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6POyKtMZDb

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:47 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 204 expanded)
%              Number of leaves         :   22 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  550 (1814 expanded)
%              Number of equality atoms :   36 ( 105 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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

thf('1',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k6_subset_1 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t123_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
          = ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k9_relat_1 @ X13 @ ( k6_subset_1 @ X14 @ X15 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X13 @ X14 ) @ ( k9_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf('7',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['5','6'])).

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
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X9 @ X10 ) @ X9 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( r1_tarski @ X16 @ ( k10_relat_1 @ X17 @ ( k9_relat_1 @ X17 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k9_relat_1 @ X13 @ ( k6_subset_1 @ X14 @ X15 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X13 @ X14 ) @ ( k9_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ ( k6_subset_1 @ sk_A @ sk_B ) @ X0 ) )
        = ( k6_subset_1 @ k1_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X9 @ X10 ) @ X9 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ ( k6_subset_1 @ sk_A @ sk_B ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','35','36','37','38'])).

thf('40',plain,
    ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['27','39'])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( r1_tarski @ ( k10_relat_1 @ X18 @ ( k9_relat_1 @ X18 @ X19 ) ) @ X19 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('42',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X9 @ X10 ) @ X9 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('49',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0
        = ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['23','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('57',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('60',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k6_subset_1 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['0','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6POyKtMZDb
% 0.13/0.37  % Computer   : n016.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 09:23:19 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 230 iterations in 0.139s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.40/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.62  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.62  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.40/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.40/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.62  thf(t157_funct_1, conjecture,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.62       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.40/0.62           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.40/0.62         ( r1_tarski @ A @ B ) ) ))).
% 0.40/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.62        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.62          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.40/0.62              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.40/0.62            ( r1_tarski @ A @ B ) ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.40/0.62  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('1', plain,
% 0.40/0.62      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(l32_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.62  thf('2', plain,
% 0.40/0.62      (![X3 : $i, X5 : $i]:
% 0.40/0.62         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.40/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.40/0.62  thf(redefinition_k6_subset_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.40/0.62  thf('3', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i]:
% 0.40/0.62         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.40/0.62      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.62  thf('4', plain,
% 0.40/0.62      (![X3 : $i, X5 : $i]:
% 0.40/0.62         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.40/0.62      inference('demod', [status(thm)], ['2', '3'])).
% 0.40/0.62  thf('5', plain,
% 0.40/0.62      (((k6_subset_1 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))
% 0.40/0.62         = (k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['1', '4'])).
% 0.40/0.62  thf(t123_funct_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.62       ( ( v2_funct_1 @ C ) =>
% 0.40/0.62         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.40/0.62           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.40/0.62  thf('6', plain,
% 0.40/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X13)
% 0.40/0.62          | ((k9_relat_1 @ X13 @ (k6_subset_1 @ X14 @ X15))
% 0.40/0.62              = (k6_subset_1 @ (k9_relat_1 @ X13 @ X14) @ 
% 0.40/0.62                 (k9_relat_1 @ X13 @ X15)))
% 0.40/0.62          | ~ (v1_funct_1 @ X13)
% 0.40/0.62          | ~ (v1_relat_1 @ X13))),
% 0.40/0.62      inference('cnf', [status(esa)], [t123_funct_1])).
% 0.40/0.62  thf('7', plain,
% 0.40/0.62      ((((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.40/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.40/0.62      inference('sup+', [status(thm)], ['5', '6'])).
% 0.40/0.62  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('10', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('11', plain,
% 0.40/0.62      (((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.40/0.62      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.40/0.62  thf('12', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(t36_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.40/0.62  thf('13', plain,
% 0.40/0.62      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.40/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.40/0.62  thf('14', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i]:
% 0.40/0.62         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.40/0.62      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.62  thf('15', plain,
% 0.40/0.62      (![X9 : $i, X10 : $i]: (r1_tarski @ (k6_subset_1 @ X9 @ X10) @ X9)),
% 0.40/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.62  thf(t1_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.40/0.62       ( r1_tarski @ A @ C ) ))).
% 0.40/0.62  thf('16', plain,
% 0.40/0.62      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.62         (~ (r1_tarski @ X6 @ X7)
% 0.40/0.62          | ~ (r1_tarski @ X7 @ X8)
% 0.40/0.62          | (r1_tarski @ X6 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.40/0.62  thf('17', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.62  thf('18', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k1_relat_1 @ sk_C))),
% 0.40/0.62      inference('sup-', [status(thm)], ['12', '17'])).
% 0.40/0.62  thf(t146_funct_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ B ) =>
% 0.40/0.62       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.40/0.62         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.40/0.62  thf('19', plain,
% 0.40/0.62      (![X16 : $i, X17 : $i]:
% 0.40/0.62         (~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 0.40/0.62          | (r1_tarski @ X16 @ (k10_relat_1 @ X17 @ (k9_relat_1 @ X17 @ X16)))
% 0.40/0.62          | ~ (v1_relat_1 @ X17))),
% 0.40/0.62      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.40/0.62  thf('20', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ sk_C)
% 0.40/0.62          | (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ 
% 0.40/0.62             (k10_relat_1 @ sk_C @ 
% 0.40/0.62              (k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.62  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('22', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ 
% 0.40/0.62          (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0))))),
% 0.40/0.62      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.62  thf('23', plain,
% 0.40/0.62      ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ 
% 0.40/0.62        (k10_relat_1 @ sk_C @ k1_xboole_0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['11', '22'])).
% 0.40/0.62  thf(d10_xboole_0, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.62  thf('24', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.62  thf('25', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.40/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.40/0.62  thf('26', plain,
% 0.40/0.62      (![X3 : $i, X5 : $i]:
% 0.40/0.62         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.40/0.62      inference('demod', [status(thm)], ['2', '3'])).
% 0.40/0.62  thf('27', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.40/0.62  thf('28', plain,
% 0.40/0.62      (((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.40/0.62      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.40/0.62  thf('29', plain,
% 0.40/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X13)
% 0.40/0.62          | ((k9_relat_1 @ X13 @ (k6_subset_1 @ X14 @ X15))
% 0.40/0.62              = (k6_subset_1 @ (k9_relat_1 @ X13 @ X14) @ 
% 0.40/0.62                 (k9_relat_1 @ X13 @ X15)))
% 0.40/0.62          | ~ (v1_funct_1 @ X13)
% 0.40/0.62          | ~ (v1_relat_1 @ X13))),
% 0.40/0.62      inference('cnf', [status(esa)], [t123_funct_1])).
% 0.40/0.62  thf('30', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (((k9_relat_1 @ sk_C @ 
% 0.40/0.62            (k6_subset_1 @ (k6_subset_1 @ sk_A @ sk_B) @ X0))
% 0.40/0.62            = (k6_subset_1 @ k1_xboole_0 @ (k9_relat_1 @ sk_C @ X0)))
% 0.40/0.62          | ~ (v1_relat_1 @ sk_C)
% 0.40/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62          | ~ (v2_funct_1 @ sk_C))),
% 0.40/0.62      inference('sup+', [status(thm)], ['28', '29'])).
% 0.40/0.62  thf('31', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.40/0.62  thf('32', plain,
% 0.40/0.62      (![X9 : $i, X10 : $i]: (r1_tarski @ (k6_subset_1 @ X9 @ X10) @ X9)),
% 0.40/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.62  thf('33', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.40/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.40/0.62  thf('34', plain,
% 0.40/0.62      (![X3 : $i, X5 : $i]:
% 0.40/0.62         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.40/0.62      inference('demod', [status(thm)], ['2', '3'])).
% 0.40/0.62  thf('35', plain,
% 0.40/0.62      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.62  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('38', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('39', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((k9_relat_1 @ sk_C @ (k6_subset_1 @ (k6_subset_1 @ sk_A @ sk_B) @ X0))
% 0.40/0.62           = (k1_xboole_0))),
% 0.40/0.62      inference('demod', [status(thm)], ['30', '35', '36', '37', '38'])).
% 0.40/0.62  thf('40', plain, (((k9_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['27', '39'])).
% 0.40/0.62  thf(t152_funct_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.62       ( ( v2_funct_1 @ B ) =>
% 0.40/0.62         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.40/0.62  thf('41', plain,
% 0.40/0.62      (![X18 : $i, X19 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X18)
% 0.40/0.62          | (r1_tarski @ (k10_relat_1 @ X18 @ (k9_relat_1 @ X18 @ X19)) @ X19)
% 0.40/0.62          | ~ (v1_funct_1 @ X18)
% 0.40/0.62          | ~ (v1_relat_1 @ X18))),
% 0.40/0.62      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.40/0.62  thf('42', plain,
% 0.40/0.62      (((r1_tarski @ (k10_relat_1 @ sk_C @ k1_xboole_0) @ k1_xboole_0)
% 0.40/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.40/0.62      inference('sup+', [status(thm)], ['40', '41'])).
% 0.40/0.62  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('45', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('46', plain,
% 0.40/0.62      ((r1_tarski @ (k10_relat_1 @ sk_C @ k1_xboole_0) @ k1_xboole_0)),
% 0.40/0.62      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.40/0.62  thf('47', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.40/0.62  thf('48', plain,
% 0.40/0.62      (![X9 : $i, X10 : $i]: (r1_tarski @ (k6_subset_1 @ X9 @ X10) @ X9)),
% 0.40/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.62  thf('49', plain,
% 0.40/0.62      (![X0 : $i, X2 : $i]:
% 0.40/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.62  thf('50', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.40/0.62          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['48', '49'])).
% 0.40/0.62  thf('51', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k6_subset_1 @ X0 @ X0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['47', '50'])).
% 0.40/0.62  thf('52', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.40/0.62  thf('53', plain,
% 0.40/0.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.40/0.62      inference('demod', [status(thm)], ['51', '52'])).
% 0.40/0.62  thf('54', plain, (((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['46', '53'])).
% 0.40/0.62  thf('55', plain, ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ k1_xboole_0)),
% 0.40/0.62      inference('demod', [status(thm)], ['23', '54'])).
% 0.40/0.62  thf('56', plain,
% 0.40/0.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.40/0.62      inference('demod', [status(thm)], ['51', '52'])).
% 0.40/0.62  thf('57', plain, (((k6_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.62  thf('58', plain,
% 0.40/0.62      (![X3 : $i, X4 : $i]:
% 0.40/0.62         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.40/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.40/0.62  thf('59', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i]:
% 0.40/0.62         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.40/0.62      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.62  thf('60', plain,
% 0.40/0.62      (![X3 : $i, X4 : $i]:
% 0.40/0.62         ((r1_tarski @ X3 @ X4) | ((k6_subset_1 @ X3 @ X4) != (k1_xboole_0)))),
% 0.40/0.62      inference('demod', [status(thm)], ['58', '59'])).
% 0.40/0.62  thf('61', plain,
% 0.40/0.62      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['57', '60'])).
% 0.40/0.62  thf('62', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.40/0.62      inference('simplify', [status(thm)], ['61'])).
% 0.40/0.62  thf('63', plain, ($false), inference('demod', [status(thm)], ['0', '62'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.40/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
