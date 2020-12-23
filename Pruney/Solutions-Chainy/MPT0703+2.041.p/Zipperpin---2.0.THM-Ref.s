%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZOLe39Jslt

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 169 expanded)
%              Number of leaves         :   22 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  529 (1416 expanded)
%              Number of equality atoms :   41 (  86 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

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

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k10_relat_1 @ X13 @ ( k6_subset_1 @ X14 @ X15 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X13 @ X14 ) @ ( k10_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('2',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k6_subset_1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','6'])).

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

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X8 @ X9 ) @ X8 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k6_subset_1 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k2_relat_1 @ X17 ) )
      | ( ( k9_relat_1 @ X17 @ ( k10_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
        = ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
      = ( k6_subset_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['10','24'])).

thf('26',plain,
    ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('29',plain,(
    ! [X10: $i] :
      ( ( k6_subset_1 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X8 @ X9 ) @ X8 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k6_subset_1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k10_relat_1 @ X13 @ ( k6_subset_1 @ X14 @ X15 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X13 @ X14 ) @ ( k10_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X8 @ X9 ) @ X8 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['26','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k6_subset_1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('43',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X10: $i] :
      ( ( k6_subset_1 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('45',plain,
    ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X8 @ X9 ) @ X8 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k2_relat_1 @ X17 ) )
      | ( ( k9_relat_1 @ X17 @ ( k10_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( k1_xboole_0
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('57',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k6_subset_1 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['0','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZOLe39Jslt
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:34:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 209 iterations in 0.061s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.51  thf(t158_funct_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.52       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.21/0.52           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.21/0.52         ( r1_tarski @ A @ B ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.52        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.52          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.21/0.52              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.21/0.52            ( r1_tarski @ A @ B ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.21/0.52  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t138_funct_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.52       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.21/0.52         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.52         (((k10_relat_1 @ X13 @ (k6_subset_1 @ X14 @ X15))
% 0.21/0.52            = (k6_subset_1 @ (k10_relat_1 @ X13 @ X14) @ 
% 0.21/0.52               (k10_relat_1 @ X13 @ X15)))
% 0.21/0.52          | ~ (v1_funct_1 @ X13)
% 0.21/0.52          | ~ (v1_relat_1 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(l32_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i]:
% 0.21/0.52         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.52  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i]:
% 0.21/0.52         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i]:
% 0.21/0.52         (((k6_subset_1 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (((k6_subset_1 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.21/0.52         (k10_relat_1 @ sk_C @ sk_B)) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      ((((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.21/0.52        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.52        | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.52      inference('sup+', [status(thm)], ['1', '6'])).
% 0.21/0.52  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.52  thf('11', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t36_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.21/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i]:
% 0.21/0.52         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]: (r1_tarski @ (k6_subset_1 @ X8 @ X9) @ X8)),
% 0.21/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf(t12_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X0) = (X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf(t11_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k6_subset_1 @ X0 @ X2) @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '18'])).
% 0.21/0.52  thf(t147_funct_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.52       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.52         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X16 @ (k2_relat_1 @ X17))
% 0.21/0.52          | ((k9_relat_1 @ X17 @ (k10_relat_1 @ X17 @ X16)) = (X16))
% 0.21/0.52          | ~ (v1_funct_1 @ X17)
% 0.21/0.52          | ~ (v1_relat_1 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ sk_C)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.52          | ((k9_relat_1 @ sk_C @ 
% 0.21/0.52              (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.21/0.52              = (k6_subset_1 @ sk_A @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.21/0.52           = (k6_subset_1 @ sk_A @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (((k9_relat_1 @ sk_C @ k1_xboole_0) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('sup+', [status(thm)], ['10', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.52  thf(t3_boole, axiom,
% 0.21/0.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.52  thf('27', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i]:
% 0.21/0.52         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.52  thf('29', plain, (![X10 : $i]: ((k6_subset_1 @ X10 @ k1_xboole_0) = (X10))),
% 0.21/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]: (r1_tarski @ (k6_subset_1 @ X8 @ X9) @ X8)),
% 0.21/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('31', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.52      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i]:
% 0.21/0.52         (((k6_subset_1 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('33', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.52         (((k10_relat_1 @ X13 @ (k6_subset_1 @ X14 @ X15))
% 0.21/0.52            = (k6_subset_1 @ (k10_relat_1 @ X13 @ X14) @ 
% 0.21/0.52               (k10_relat_1 @ X13 @ X15)))
% 0.21/0.52          | ~ (v1_funct_1 @ X13)
% 0.21/0.52          | ~ (v1_relat_1 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]: (r1_tarski @ (k6_subset_1 @ X8 @ X9) @ X8)),
% 0.21/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((r1_tarski @ (k10_relat_1 @ X2 @ (k6_subset_1 @ X1 @ X0)) @ 
% 0.21/0.52           (k10_relat_1 @ X2 @ X1))
% 0.21/0.52          | ~ (v1_relat_1 @ X2)
% 0.21/0.52          | ~ (v1_funct_1 @ X2))),
% 0.21/0.52      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_tarski @ (k10_relat_1 @ X1 @ k1_xboole_0) @ 
% 0.21/0.52           (k10_relat_1 @ X1 @ X0))
% 0.21/0.52          | ~ (v1_funct_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['33', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (((r1_tarski @ (k10_relat_1 @ sk_C @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.52        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.52        | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.52      inference('sup+', [status(thm)], ['26', '37'])).
% 0.21/0.52  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      ((r1_tarski @ (k10_relat_1 @ sk_C @ k1_xboole_0) @ k1_xboole_0)),
% 0.21/0.52      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i]:
% 0.21/0.52         (((k6_subset_1 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (((k6_subset_1 @ (k10_relat_1 @ sk_C @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.52         = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.52  thf('44', plain, (![X10 : $i]: ((k6_subset_1 @ X10 @ k1_xboole_0) = (X10))),
% 0.21/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.52  thf('45', plain, (((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.52  thf('46', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]: (r1_tarski @ (k6_subset_1 @ X8 @ X9) @ X8)),
% 0.21/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('48', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.52      inference('sup+', [status(thm)], ['46', '47'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X16 @ (k2_relat_1 @ X17))
% 0.21/0.52          | ((k9_relat_1 @ X17 @ (k10_relat_1 @ X17 @ X16)) = (X16))
% 0.21/0.52          | ~ (v1_funct_1 @ X17)
% 0.21/0.52          | ~ (v1_relat_1 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.52              = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      ((((k9_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.52        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.52      inference('sup+', [status(thm)], ['45', '50'])).
% 0.21/0.52  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('54', plain, (((k9_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.21/0.52  thf('55', plain, (((k1_xboole_0) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '54'])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i]:
% 0.21/0.52         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_tarski @ X0 @ X1) | ((k6_subset_1 @ X0 @ X1) != (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['55', '58'])).
% 0.21/0.52  thf('60', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.52      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.52  thf('61', plain, ($false), inference('demod', [status(thm)], ['0', '60'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
