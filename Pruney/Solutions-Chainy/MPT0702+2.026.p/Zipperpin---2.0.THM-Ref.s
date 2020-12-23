%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hj1TvSPBDH

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:45 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 146 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :   17
%              Number of atoms          :  573 (1420 expanded)
%              Number of equality atoms :   32 (  53 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k9_relat_1 @ X17 @ ( k6_subset_1 @ X18 @ X19 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X17 @ X18 ) @ ( k9_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k6_subset_1 @ X6 @ X8 ) @ X7 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( r1_tarski @ X20 @ ( k10_relat_1 @ X21 @ ( k9_relat_1 @ X21 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k9_relat_1 @ X17 @ ( k6_subset_1 @ X18 @ X19 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X17 @ X18 ) @ ( k9_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k9_relat_1 @ X17 @ ( k6_subset_1 @ X18 @ X19 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X17 @ X18 ) @ ( k9_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf('28',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k6_subset_1 @ X6 @ X8 ) @ X7 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k9_relat_1 @ sk_C @ sk_A ) @ X0 ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ k1_xboole_0 ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['26','35'])).

thf('37',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('38',plain,
    ( ( k6_subset_1 @ ( k9_relat_1 @ sk_C @ k1_xboole_0 ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ k1_xboole_0 @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['22','38'])).

thf('40',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('41',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k6_subset_1 @ X6 @ X8 ) @ X7 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('43',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['39','44','45','46','47'])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('49',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( r1_tarski @ ( k10_relat_1 @ X22 @ ( k9_relat_1 @ X22 @ X23 ) ) @ X23 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('50',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('56',plain,
    ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['21','56'])).

thf('58',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('59',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('61',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('62',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k6_subset_1 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['0','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hj1TvSPBDH
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:54:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.60  % Solved by: fo/fo7.sh
% 0.36/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.60  % done 316 iterations in 0.145s
% 0.36/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.60  % SZS output start Refutation
% 0.36/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.60  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.36/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.60  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.36/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.60  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.36/0.60  thf(t157_funct_1, conjecture,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.60       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.36/0.60           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.36/0.60         ( r1_tarski @ A @ B ) ) ))).
% 0.36/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.60        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.60          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.36/0.60              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.36/0.60            ( r1_tarski @ A @ B ) ) ) )),
% 0.36/0.60    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.36/0.60  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('1', plain,
% 0.36/0.60      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(l32_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.60  thf('2', plain,
% 0.36/0.60      (![X3 : $i, X5 : $i]:
% 0.36/0.60         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.36/0.60      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.60  thf(redefinition_k6_subset_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.36/0.60  thf('3', plain,
% 0.36/0.60      (![X15 : $i, X16 : $i]:
% 0.36/0.60         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 0.36/0.60      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.36/0.60  thf('4', plain,
% 0.36/0.60      (![X3 : $i, X5 : $i]:
% 0.36/0.60         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.36/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.60  thf('5', plain,
% 0.36/0.60      (((k6_subset_1 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))
% 0.36/0.60         = (k1_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['1', '4'])).
% 0.36/0.60  thf(t123_funct_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.60       ( ( v2_funct_1 @ C ) =>
% 0.36/0.60         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.36/0.60           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.36/0.60  thf('6', plain,
% 0.36/0.60      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.60         (~ (v2_funct_1 @ X17)
% 0.36/0.60          | ((k9_relat_1 @ X17 @ (k6_subset_1 @ X18 @ X19))
% 0.36/0.60              = (k6_subset_1 @ (k9_relat_1 @ X17 @ X18) @ 
% 0.36/0.60                 (k9_relat_1 @ X17 @ X19)))
% 0.36/0.60          | ~ (v1_funct_1 @ X17)
% 0.36/0.60          | ~ (v1_relat_1 @ X17))),
% 0.36/0.60      inference('cnf', [status(esa)], [t123_funct_1])).
% 0.36/0.60  thf('7', plain,
% 0.36/0.60      ((((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.36/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.60      inference('sup+', [status(thm)], ['5', '6'])).
% 0.36/0.60  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('10', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('11', plain,
% 0.36/0.60      (((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.36/0.60      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.36/0.60  thf('12', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(t109_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.36/0.60  thf('13', plain,
% 0.36/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k4_xboole_0 @ X6 @ X8) @ X7))),
% 0.36/0.60      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.36/0.60  thf('14', plain,
% 0.36/0.60      (![X15 : $i, X16 : $i]:
% 0.36/0.60         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 0.36/0.60      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.36/0.60  thf('15', plain,
% 0.36/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k6_subset_1 @ X6 @ X8) @ X7))),
% 0.36/0.60      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.60  thf('16', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k1_relat_1 @ sk_C))),
% 0.36/0.60      inference('sup-', [status(thm)], ['12', '15'])).
% 0.36/0.60  thf(t146_funct_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ B ) =>
% 0.36/0.60       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.36/0.60         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.36/0.60  thf('17', plain,
% 0.36/0.60      (![X20 : $i, X21 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 0.36/0.60          | (r1_tarski @ X20 @ (k10_relat_1 @ X21 @ (k9_relat_1 @ X21 @ X20)))
% 0.36/0.60          | ~ (v1_relat_1 @ X21))),
% 0.36/0.60      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.36/0.60  thf('18', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (~ (v1_relat_1 @ sk_C)
% 0.36/0.60          | (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ 
% 0.36/0.60             (k10_relat_1 @ sk_C @ 
% 0.36/0.60              (k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.60  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('20', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ 
% 0.36/0.60          (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0))))),
% 0.36/0.60      inference('demod', [status(thm)], ['18', '19'])).
% 0.36/0.60  thf('21', plain,
% 0.36/0.60      ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ 
% 0.36/0.60        (k10_relat_1 @ sk_C @ k1_xboole_0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['11', '20'])).
% 0.36/0.60  thf('22', plain,
% 0.36/0.60      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.60         (~ (v2_funct_1 @ X17)
% 0.36/0.60          | ((k9_relat_1 @ X17 @ (k6_subset_1 @ X18 @ X19))
% 0.36/0.60              = (k6_subset_1 @ (k9_relat_1 @ X17 @ X18) @ 
% 0.36/0.60                 (k9_relat_1 @ X17 @ X19)))
% 0.36/0.60          | ~ (v1_funct_1 @ X17)
% 0.36/0.60          | ~ (v1_relat_1 @ X17))),
% 0.36/0.60      inference('cnf', [status(esa)], [t123_funct_1])).
% 0.36/0.60  thf(d10_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.60  thf('23', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.36/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.60  thf('24', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.60      inference('simplify', [status(thm)], ['23'])).
% 0.36/0.60  thf('25', plain,
% 0.36/0.60      (![X3 : $i, X5 : $i]:
% 0.36/0.60         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.36/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.60  thf('26', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.60  thf('27', plain,
% 0.36/0.60      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.60         (~ (v2_funct_1 @ X17)
% 0.36/0.60          | ((k9_relat_1 @ X17 @ (k6_subset_1 @ X18 @ X19))
% 0.36/0.60              = (k6_subset_1 @ (k9_relat_1 @ X17 @ X18) @ 
% 0.36/0.60                 (k9_relat_1 @ X17 @ X19)))
% 0.36/0.60          | ~ (v1_funct_1 @ X17)
% 0.36/0.60          | ~ (v1_relat_1 @ X17))),
% 0.36/0.60      inference('cnf', [status(esa)], [t123_funct_1])).
% 0.36/0.60  thf('28', plain,
% 0.36/0.60      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('29', plain,
% 0.36/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k6_subset_1 @ X6 @ X8) @ X7))),
% 0.36/0.60      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.60  thf('30', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (r1_tarski @ (k6_subset_1 @ (k9_relat_1 @ sk_C @ sk_A) @ X0) @ 
% 0.36/0.60          (k9_relat_1 @ sk_C @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.60  thf('31', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((r1_tarski @ (k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)) @ 
% 0.36/0.60           (k9_relat_1 @ sk_C @ sk_B))
% 0.36/0.60          | ~ (v1_relat_1 @ sk_C)
% 0.36/0.60          | ~ (v1_funct_1 @ sk_C)
% 0.36/0.60          | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.60      inference('sup+', [status(thm)], ['27', '30'])).
% 0.36/0.60  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('34', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('35', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (r1_tarski @ (k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)) @ 
% 0.36/0.60          (k9_relat_1 @ sk_C @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.36/0.60  thf('36', plain,
% 0.36/0.60      ((r1_tarski @ (k9_relat_1 @ sk_C @ k1_xboole_0) @ 
% 0.36/0.60        (k9_relat_1 @ sk_C @ sk_B))),
% 0.36/0.60      inference('sup+', [status(thm)], ['26', '35'])).
% 0.36/0.60  thf('37', plain,
% 0.36/0.60      (![X3 : $i, X5 : $i]:
% 0.36/0.60         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.36/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.60  thf('38', plain,
% 0.36/0.60      (((k6_subset_1 @ (k9_relat_1 @ sk_C @ k1_xboole_0) @ 
% 0.36/0.60         (k9_relat_1 @ sk_C @ sk_B)) = (k1_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.60  thf('39', plain,
% 0.36/0.60      ((((k9_relat_1 @ sk_C @ (k6_subset_1 @ k1_xboole_0 @ sk_B))
% 0.36/0.60          = (k1_xboole_0))
% 0.36/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.60      inference('sup+', [status(thm)], ['22', '38'])).
% 0.36/0.60  thf('40', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.60      inference('simplify', [status(thm)], ['23'])).
% 0.36/0.60  thf('41', plain,
% 0.36/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k6_subset_1 @ X6 @ X8) @ X7))),
% 0.36/0.60      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.60  thf('42', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 0.36/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.60  thf(t3_xboole_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.60  thf('43', plain,
% 0.36/0.60      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ k1_xboole_0))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.36/0.60  thf('44', plain,
% 0.36/0.60      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['42', '43'])).
% 0.36/0.60  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('48', plain, (((k9_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.60      inference('demod', [status(thm)], ['39', '44', '45', '46', '47'])).
% 0.36/0.60  thf(t152_funct_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.60       ( ( v2_funct_1 @ B ) =>
% 0.36/0.60         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.36/0.60  thf('49', plain,
% 0.36/0.60      (![X22 : $i, X23 : $i]:
% 0.36/0.60         (~ (v2_funct_1 @ X22)
% 0.36/0.60          | (r1_tarski @ (k10_relat_1 @ X22 @ (k9_relat_1 @ X22 @ X23)) @ X23)
% 0.36/0.60          | ~ (v1_funct_1 @ X22)
% 0.36/0.60          | ~ (v1_relat_1 @ X22))),
% 0.36/0.60      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.36/0.60  thf('50', plain,
% 0.36/0.60      (((r1_tarski @ (k10_relat_1 @ sk_C @ k1_xboole_0) @ k1_xboole_0)
% 0.36/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.60      inference('sup+', [status(thm)], ['48', '49'])).
% 0.36/0.60  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('53', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('54', plain,
% 0.36/0.60      ((r1_tarski @ (k10_relat_1 @ sk_C @ k1_xboole_0) @ k1_xboole_0)),
% 0.36/0.60      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.36/0.60  thf('55', plain,
% 0.36/0.60      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ k1_xboole_0))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.36/0.60  thf('56', plain, (((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.60  thf('57', plain, ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ k1_xboole_0)),
% 0.36/0.60      inference('demod', [status(thm)], ['21', '56'])).
% 0.36/0.60  thf('58', plain,
% 0.36/0.60      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ k1_xboole_0))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.36/0.60  thf('59', plain, (((k6_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.60  thf('60', plain,
% 0.36/0.60      (![X3 : $i, X4 : $i]:
% 0.36/0.60         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.36/0.60      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.60  thf('61', plain,
% 0.36/0.60      (![X15 : $i, X16 : $i]:
% 0.36/0.60         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 0.36/0.60      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.36/0.60  thf('62', plain,
% 0.36/0.60      (![X3 : $i, X4 : $i]:
% 0.36/0.60         ((r1_tarski @ X3 @ X4) | ((k6_subset_1 @ X3 @ X4) != (k1_xboole_0)))),
% 0.36/0.60      inference('demod', [status(thm)], ['60', '61'])).
% 0.36/0.60  thf('63', plain,
% 0.36/0.60      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['59', '62'])).
% 0.36/0.60  thf('64', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.36/0.60      inference('simplify', [status(thm)], ['63'])).
% 0.36/0.60  thf('65', plain, ($false), inference('demod', [status(thm)], ['0', '64'])).
% 0.36/0.60  
% 0.36/0.60  % SZS output end Refutation
% 0.36/0.60  
% 0.36/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
