%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CIqtHWPd9r

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:53 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 168 expanded)
%              Number of leaves         :   25 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  574 (1396 expanded)
%              Number of equality atoms :   32 (  58 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k6_subset_1 @ X25 @ X26 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X24 @ X25 ) @ ( k10_relat_1 @ X24 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k2_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k6_subset_1 @ X22 @ X23 )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X12 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) @ X0 ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k6_subset_1 @ X22 @ X23 )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X10 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('26',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X27 @ ( k2_relat_1 @ X28 ) )
      | ( ( k9_relat_1 @ X28 @ ( k10_relat_1 @ X28 @ X27 ) )
        = X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
        = ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
      = ( k6_subset_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['18','30'])).

thf('32',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k6_subset_1 @ X25 @ X26 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X24 @ X25 ) @ ( k10_relat_1 @ X24 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('33',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X12 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
      = ( k6_subset_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('40',plain,
    ( ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
      = ( k6_subset_1 @ sk_A @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,
    ( k1_xboole_0
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('49',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k6_subset_1 @ X22 @ X23 )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('50',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('54',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('55',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19
        = ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('56',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k6_subset_1 @ X22 @ X23 )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('57',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19
        = ( k2_xboole_0 @ X18 @ ( k6_subset_1 @ X19 @ X18 ) ) )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['52','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['0','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CIqtHWPd9r
% 0.16/0.40  % Computer   : n010.cluster.edu
% 0.16/0.40  % Model      : x86_64 x86_64
% 0.16/0.40  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.40  % Memory     : 8042.1875MB
% 0.16/0.40  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.40  % CPULimit   : 60
% 0.16/0.40  % DateTime   : Tue Dec  1 09:27:30 EST 2020
% 0.16/0.40  % CPUTime    : 
% 0.16/0.40  % Running portfolio for 600 s
% 0.16/0.40  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.40  % Number of cores: 8
% 0.16/0.40  % Python version: Python 3.6.8
% 0.16/0.40  % Running in FO mode
% 0.84/1.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.84/1.04  % Solved by: fo/fo7.sh
% 0.84/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.04  % done 1093 iterations in 0.525s
% 0.84/1.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.84/1.04  % SZS output start Refutation
% 0.84/1.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.84/1.04  thf(sk_C_type, type, sk_C: $i).
% 0.84/1.04  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.84/1.04  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.84/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.04  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.84/1.04  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.84/1.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.04  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.84/1.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.84/1.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.84/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.04  thf(t158_funct_1, conjecture,
% 0.84/1.04    (![A:$i,B:$i,C:$i]:
% 0.84/1.04     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.84/1.04       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.84/1.04           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.84/1.04         ( r1_tarski @ A @ B ) ) ))).
% 0.84/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.04    (~( ![A:$i,B:$i,C:$i]:
% 0.84/1.04        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.84/1.04          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.84/1.04              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.84/1.04            ( r1_tarski @ A @ B ) ) ) )),
% 0.84/1.04    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.84/1.04  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf(t138_funct_1, axiom,
% 0.84/1.04    (![A:$i,B:$i,C:$i]:
% 0.84/1.04     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.84/1.04       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.84/1.04         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.84/1.04  thf('1', plain,
% 0.84/1.04      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.84/1.04         (((k10_relat_1 @ X24 @ (k6_subset_1 @ X25 @ X26))
% 0.84/1.04            = (k6_subset_1 @ (k10_relat_1 @ X24 @ X25) @ 
% 0.84/1.04               (k10_relat_1 @ X24 @ X26)))
% 0.84/1.04          | ~ (v1_funct_1 @ X24)
% 0.84/1.04          | ~ (v1_relat_1 @ X24))),
% 0.84/1.04      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.84/1.04  thf(t7_xboole_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.84/1.04  thf('2', plain,
% 0.84/1.04      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.84/1.04      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.84/1.04  thf('3', plain,
% 0.84/1.04      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf(t1_xboole_1, axiom,
% 0.84/1.04    (![A:$i,B:$i,C:$i]:
% 0.84/1.04     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.84/1.04       ( r1_tarski @ A @ C ) ))).
% 0.84/1.04  thf('4', plain,
% 0.84/1.04      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.84/1.04         (~ (r1_tarski @ X6 @ X7)
% 0.84/1.04          | ~ (r1_tarski @ X7 @ X8)
% 0.84/1.04          | (r1_tarski @ X6 @ X8))),
% 0.84/1.04      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.84/1.04  thf('5', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ X0)
% 0.84/1.04          | ~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_B) @ X0))),
% 0.84/1.04      inference('sup-', [status(thm)], ['3', '4'])).
% 0.84/1.04  thf('6', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.84/1.04          (k2_xboole_0 @ (k10_relat_1 @ sk_C @ sk_B) @ X0))),
% 0.84/1.04      inference('sup-', [status(thm)], ['2', '5'])).
% 0.84/1.04  thf(t43_xboole_1, axiom,
% 0.84/1.04    (![A:$i,B:$i,C:$i]:
% 0.84/1.04     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.84/1.04       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.84/1.04  thf('7', plain,
% 0.84/1.04      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.84/1.04         ((r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.84/1.04          | ~ (r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.84/1.04      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.84/1.04  thf(redefinition_k6_subset_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.84/1.04  thf('8', plain,
% 0.84/1.04      (![X22 : $i, X23 : $i]:
% 0.84/1.04         ((k6_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))),
% 0.84/1.04      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.04  thf('9', plain,
% 0.84/1.04      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.84/1.04         ((r1_tarski @ (k6_subset_1 @ X12 @ X13) @ X14)
% 0.84/1.04          | ~ (r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.84/1.04      inference('demod', [status(thm)], ['7', '8'])).
% 0.84/1.04  thf('10', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         (r1_tarski @ 
% 0.84/1.04          (k6_subset_1 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.84/1.04           (k10_relat_1 @ sk_C @ sk_B)) @ 
% 0.84/1.04          X0)),
% 0.84/1.04      inference('sup-', [status(thm)], ['6', '9'])).
% 0.84/1.04  thf('11', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         ((r1_tarski @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) @ X0)
% 0.84/1.04          | ~ (v1_relat_1 @ sk_C)
% 0.84/1.04          | ~ (v1_funct_1 @ sk_C))),
% 0.84/1.04      inference('sup+', [status(thm)], ['1', '10'])).
% 0.84/1.04  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('14', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         (r1_tarski @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) @ X0)),
% 0.84/1.04      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.84/1.04  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.84/1.04  thf('15', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.84/1.04      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.84/1.04  thf(d10_xboole_0, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.84/1.04  thf('16', plain,
% 0.84/1.04      (![X0 : $i, X2 : $i]:
% 0.84/1.04         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.84/1.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.84/1.04  thf('17', plain,
% 0.84/1.04      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['15', '16'])).
% 0.84/1.04  thf('18', plain,
% 0.84/1.04      (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.84/1.04      inference('sup-', [status(thm)], ['14', '17'])).
% 0.84/1.04  thf('19', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf(t36_xboole_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.84/1.04  thf('20', plain,
% 0.84/1.04      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.84/1.04      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.84/1.04  thf('21', plain,
% 0.84/1.04      (![X22 : $i, X23 : $i]:
% 0.84/1.04         ((k6_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))),
% 0.84/1.04      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.04  thf('22', plain,
% 0.84/1.04      (![X10 : $i, X11 : $i]: (r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X10)),
% 0.84/1.04      inference('demod', [status(thm)], ['20', '21'])).
% 0.84/1.04  thf('23', plain,
% 0.84/1.04      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.84/1.04         (~ (r1_tarski @ X6 @ X7)
% 0.84/1.04          | ~ (r1_tarski @ X7 @ X8)
% 0.84/1.04          | (r1_tarski @ X6 @ X8))),
% 0.84/1.04      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.84/1.04  thf('24', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.04         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.84/1.04      inference('sup-', [status(thm)], ['22', '23'])).
% 0.84/1.04  thf('25', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_C))),
% 0.84/1.04      inference('sup-', [status(thm)], ['19', '24'])).
% 0.84/1.04  thf(t147_funct_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.84/1.04       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.84/1.04         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.84/1.04  thf('26', plain,
% 0.84/1.04      (![X27 : $i, X28 : $i]:
% 0.84/1.04         (~ (r1_tarski @ X27 @ (k2_relat_1 @ X28))
% 0.84/1.04          | ((k9_relat_1 @ X28 @ (k10_relat_1 @ X28 @ X27)) = (X27))
% 0.84/1.04          | ~ (v1_funct_1 @ X28)
% 0.84/1.04          | ~ (v1_relat_1 @ X28))),
% 0.84/1.04      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.84/1.04  thf('27', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ sk_C)
% 0.84/1.04          | ~ (v1_funct_1 @ sk_C)
% 0.84/1.04          | ((k9_relat_1 @ sk_C @ 
% 0.84/1.04              (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.84/1.04              = (k6_subset_1 @ sk_A @ X0)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['25', '26'])).
% 0.84/1.04  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('30', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.84/1.04           = (k6_subset_1 @ sk_A @ X0))),
% 0.84/1.04      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.84/1.04  thf('31', plain,
% 0.84/1.04      (((k9_relat_1 @ sk_C @ k1_xboole_0) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.84/1.04      inference('sup+', [status(thm)], ['18', '30'])).
% 0.84/1.04  thf('32', plain,
% 0.84/1.04      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.84/1.04         (((k10_relat_1 @ X24 @ (k6_subset_1 @ X25 @ X26))
% 0.84/1.04            = (k6_subset_1 @ (k10_relat_1 @ X24 @ X25) @ 
% 0.84/1.04               (k10_relat_1 @ X24 @ X26)))
% 0.84/1.04          | ~ (v1_funct_1 @ X24)
% 0.84/1.04          | ~ (v1_relat_1 @ X24))),
% 0.84/1.04      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.84/1.04  thf('33', plain,
% 0.84/1.04      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.84/1.04      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.84/1.04  thf('34', plain,
% 0.84/1.04      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.84/1.04         ((r1_tarski @ (k6_subset_1 @ X12 @ X13) @ X14)
% 0.84/1.04          | ~ (r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.84/1.04      inference('demod', [status(thm)], ['7', '8'])).
% 0.84/1.04  thf('35', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X1 @ X1) @ X0)),
% 0.84/1.04      inference('sup-', [status(thm)], ['33', '34'])).
% 0.84/1.04  thf('36', plain,
% 0.84/1.04      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['15', '16'])).
% 0.84/1.04  thf('37', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.84/1.04      inference('sup-', [status(thm)], ['35', '36'])).
% 0.84/1.04  thf('38', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         (((k10_relat_1 @ X1 @ (k6_subset_1 @ X0 @ X0)) = (k1_xboole_0))
% 0.84/1.04          | ~ (v1_relat_1 @ X1)
% 0.84/1.04          | ~ (v1_funct_1 @ X1))),
% 0.84/1.04      inference('sup+', [status(thm)], ['32', '37'])).
% 0.84/1.04  thf('39', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.84/1.04           = (k6_subset_1 @ sk_A @ X0))),
% 0.84/1.04      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.84/1.04  thf('40', plain,
% 0.84/1.04      ((((k9_relat_1 @ sk_C @ k1_xboole_0) = (k6_subset_1 @ sk_A @ sk_A))
% 0.84/1.04        | ~ (v1_funct_1 @ sk_C)
% 0.84/1.04        | ~ (v1_relat_1 @ sk_C))),
% 0.84/1.04      inference('sup+', [status(thm)], ['38', '39'])).
% 0.84/1.04  thf('41', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.84/1.04      inference('sup-', [status(thm)], ['35', '36'])).
% 0.84/1.04  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('44', plain, (((k9_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.84/1.04      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.84/1.04  thf('45', plain, (((k1_xboole_0) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.84/1.04      inference('demod', [status(thm)], ['31', '44'])).
% 0.84/1.04  thf('46', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.84/1.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.84/1.04  thf('47', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.84/1.04      inference('simplify', [status(thm)], ['46'])).
% 0.84/1.04  thf(t44_xboole_1, axiom,
% 0.84/1.04    (![A:$i,B:$i,C:$i]:
% 0.84/1.04     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.84/1.04       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.84/1.04  thf('48', plain,
% 0.84/1.04      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.84/1.04         ((r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 0.84/1.04          | ~ (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17))),
% 0.84/1.04      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.84/1.04  thf('49', plain,
% 0.84/1.04      (![X22 : $i, X23 : $i]:
% 0.84/1.04         ((k6_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))),
% 0.84/1.04      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.04  thf('50', plain,
% 0.84/1.04      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.84/1.04         ((r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 0.84/1.04          | ~ (r1_tarski @ (k6_subset_1 @ X15 @ X16) @ X17))),
% 0.84/1.04      inference('demod', [status(thm)], ['48', '49'])).
% 0.84/1.04  thf('51', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['47', '50'])).
% 0.84/1.04  thf('52', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.84/1.04      inference('sup+', [status(thm)], ['45', '51'])).
% 0.84/1.04  thf('53', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.84/1.04      inference('sup-', [status(thm)], ['35', '36'])).
% 0.84/1.04  thf('54', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.84/1.04      inference('simplify', [status(thm)], ['46'])).
% 0.84/1.04  thf(t45_xboole_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( r1_tarski @ A @ B ) =>
% 0.84/1.04       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.84/1.04  thf('55', plain,
% 0.84/1.04      (![X18 : $i, X19 : $i]:
% 0.84/1.04         (((X19) = (k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))
% 0.84/1.04          | ~ (r1_tarski @ X18 @ X19))),
% 0.84/1.04      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.84/1.04  thf('56', plain,
% 0.84/1.04      (![X22 : $i, X23 : $i]:
% 0.84/1.04         ((k6_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))),
% 0.84/1.04      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.04  thf('57', plain,
% 0.84/1.04      (![X18 : $i, X19 : $i]:
% 0.84/1.04         (((X19) = (k2_xboole_0 @ X18 @ (k6_subset_1 @ X19 @ X18)))
% 0.84/1.04          | ~ (r1_tarski @ X18 @ X19))),
% 0.84/1.04      inference('demod', [status(thm)], ['55', '56'])).
% 0.84/1.04  thf('58', plain,
% 0.84/1.04      (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X0)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['54', '57'])).
% 0.84/1.04  thf('59', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.84/1.04      inference('sup+', [status(thm)], ['53', '58'])).
% 0.84/1.04  thf('60', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.84/1.04      inference('demod', [status(thm)], ['52', '59'])).
% 0.84/1.04  thf('61', plain, ($false), inference('demod', [status(thm)], ['0', '60'])).
% 0.84/1.04  
% 0.84/1.04  % SZS output end Refutation
% 0.84/1.04  
% 0.84/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
