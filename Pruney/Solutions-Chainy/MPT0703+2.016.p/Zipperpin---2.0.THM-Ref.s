%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eipeDyUHag

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:51 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 196 expanded)
%              Number of leaves         :   26 (  73 expanded)
%              Depth                    :   18
%              Number of atoms          :  764 (1642 expanded)
%              Number of equality atoms :   63 ( 122 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ ( k6_subset_1 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k6_subset_1 @ X25 @ X26 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X24 @ X25 ) @ ( k10_relat_1 @ X24 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('6',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k6_subset_1 @ X25 @ X26 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X24 @ X25 ) @ ( k10_relat_1 @ X24 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ sk_A @ sk_B ) ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ sk_A @ sk_B ) ) )
      = ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ( r1_tarski @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ ( k6_subset_1 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ ( k6_subset_1 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('32',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','30','33'])).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ ( k6_subset_1 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k6_subset_1 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X14 @ X15 ) @ X14 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( X0
      = ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ sk_A @ sk_B ) ) )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['19','47'])).

thf('49',plain,
    ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['4','48'])).

thf('50',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ ( k6_subset_1 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X14 @ X15 ) @ X14 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('56',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('59',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X27 @ ( k2_relat_1 @ X28 ) )
      | ( ( k9_relat_1 @ X28 @ ( k10_relat_1 @ X28 @ X27 ) )
        = X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
        = ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['49','63'])).

thf('65',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X27 @ ( k2_relat_1 @ X28 ) )
      | ( ( k9_relat_1 @ X28 @ ( k10_relat_1 @ X28 @ X27 ) )
        = X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['64','70'])).

thf('72',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ ( k6_subset_1 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('73',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('74',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('75',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ ( k6_subset_1 @ X17 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k6_subset_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,
    ( ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ sk_A )
    | ( ( k6_subset_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X14 @ X15 ) @ X14 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('79',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k6_subset_1 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('81',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eipeDyUHag
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:54:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.49/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.75  % Solved by: fo/fo7.sh
% 0.49/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.75  % done 924 iterations in 0.285s
% 0.49/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.75  % SZS output start Refutation
% 0.49/0.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.75  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.49/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.75  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.49/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.75  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.49/0.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.49/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.75  thf(t158_funct_1, conjecture,
% 0.49/0.75    (![A:$i,B:$i,C:$i]:
% 0.49/0.75     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.49/0.75       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.49/0.75           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.49/0.75         ( r1_tarski @ A @ B ) ) ))).
% 0.49/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.75    (~( ![A:$i,B:$i,C:$i]:
% 0.49/0.75        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.49/0.75          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.49/0.75              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.49/0.75            ( r1_tarski @ A @ B ) ) ) )),
% 0.49/0.75    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.49/0.75  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.49/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.75  thf(t48_xboole_1, axiom,
% 0.49/0.75    (![A:$i,B:$i]:
% 0.49/0.75     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.49/0.75  thf('1', plain,
% 0.49/0.75      (![X18 : $i, X19 : $i]:
% 0.49/0.75         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.49/0.75           = (k3_xboole_0 @ X18 @ X19))),
% 0.49/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.75  thf(redefinition_k6_subset_1, axiom,
% 0.49/0.75    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.49/0.75  thf('2', plain,
% 0.49/0.75      (![X20 : $i, X21 : $i]:
% 0.49/0.75         ((k6_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))),
% 0.49/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.49/0.75  thf('3', plain,
% 0.49/0.75      (![X20 : $i, X21 : $i]:
% 0.49/0.75         ((k6_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))),
% 0.49/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.49/0.75  thf('4', plain,
% 0.49/0.75      (![X18 : $i, X19 : $i]:
% 0.49/0.75         ((k6_subset_1 @ X18 @ (k6_subset_1 @ X18 @ X19))
% 0.49/0.75           = (k3_xboole_0 @ X18 @ X19))),
% 0.49/0.75      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.49/0.75  thf(t138_funct_1, axiom,
% 0.49/0.75    (![A:$i,B:$i,C:$i]:
% 0.49/0.75     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.49/0.75       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.49/0.75         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.49/0.75  thf('5', plain,
% 0.49/0.75      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.49/0.75         (((k10_relat_1 @ X24 @ (k6_subset_1 @ X25 @ X26))
% 0.49/0.75            = (k6_subset_1 @ (k10_relat_1 @ X24 @ X25) @ 
% 0.49/0.75               (k10_relat_1 @ X24 @ X26)))
% 0.49/0.75          | ~ (v1_funct_1 @ X24)
% 0.49/0.75          | ~ (v1_relat_1 @ X24))),
% 0.49/0.75      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.49/0.75  thf('6', plain,
% 0.49/0.75      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.49/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.75  thf(l32_xboole_1, axiom,
% 0.49/0.75    (![A:$i,B:$i]:
% 0.49/0.75     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.49/0.75  thf('7', plain,
% 0.49/0.75      (![X3 : $i, X5 : $i]:
% 0.49/0.75         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.49/0.75      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.49/0.75  thf('8', plain,
% 0.49/0.75      (![X20 : $i, X21 : $i]:
% 0.49/0.75         ((k6_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))),
% 0.49/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.49/0.75  thf('9', plain,
% 0.49/0.75      (![X3 : $i, X5 : $i]:
% 0.49/0.75         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.49/0.75      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.75  thf('10', plain,
% 0.49/0.75      (((k6_subset_1 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.49/0.75         (k10_relat_1 @ sk_C @ sk_B)) = (k1_xboole_0))),
% 0.49/0.75      inference('sup-', [status(thm)], ['6', '9'])).
% 0.49/0.75  thf('11', plain,
% 0.49/0.75      ((((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.49/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.75        | ~ (v1_funct_1 @ sk_C))),
% 0.49/0.75      inference('sup+', [status(thm)], ['5', '10'])).
% 0.49/0.75  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.75  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.75  thf('14', plain,
% 0.49/0.75      (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.49/0.75      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.49/0.75  thf('15', plain,
% 0.49/0.75      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.49/0.75         (((k10_relat_1 @ X24 @ (k6_subset_1 @ X25 @ X26))
% 0.49/0.75            = (k6_subset_1 @ (k10_relat_1 @ X24 @ X25) @ 
% 0.49/0.75               (k10_relat_1 @ X24 @ X26)))
% 0.49/0.75          | ~ (v1_funct_1 @ X24)
% 0.49/0.75          | ~ (v1_relat_1 @ X24))),
% 0.49/0.75      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.49/0.75  thf('16', plain,
% 0.49/0.75      (![X0 : $i]:
% 0.49/0.75         (((k10_relat_1 @ sk_C @ 
% 0.49/0.75            (k6_subset_1 @ X0 @ (k6_subset_1 @ sk_A @ sk_B)))
% 0.49/0.75            = (k6_subset_1 @ (k10_relat_1 @ sk_C @ X0) @ k1_xboole_0))
% 0.49/0.75          | ~ (v1_relat_1 @ sk_C)
% 0.49/0.75          | ~ (v1_funct_1 @ sk_C))),
% 0.49/0.75      inference('sup+', [status(thm)], ['14', '15'])).
% 0.49/0.75  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.75  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.75  thf('19', plain,
% 0.49/0.75      (![X0 : $i]:
% 0.49/0.75         ((k10_relat_1 @ sk_C @ 
% 0.49/0.75           (k6_subset_1 @ X0 @ (k6_subset_1 @ sk_A @ sk_B)))
% 0.49/0.75           = (k6_subset_1 @ (k10_relat_1 @ sk_C @ X0) @ k1_xboole_0))),
% 0.49/0.75      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.49/0.75  thf(d10_xboole_0, axiom,
% 0.49/0.75    (![A:$i,B:$i]:
% 0.49/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.49/0.75  thf('20', plain,
% 0.49/0.75      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.49/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.49/0.75  thf('21', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.49/0.75      inference('simplify', [status(thm)], ['20'])).
% 0.49/0.75  thf('22', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.49/0.75      inference('simplify', [status(thm)], ['20'])).
% 0.49/0.75  thf(t19_xboole_1, axiom,
% 0.49/0.75    (![A:$i,B:$i,C:$i]:
% 0.49/0.75     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.49/0.75       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.49/0.75  thf('23', plain,
% 0.49/0.75      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.75         (~ (r1_tarski @ X11 @ X12)
% 0.49/0.75          | ~ (r1_tarski @ X11 @ X13)
% 0.49/0.75          | (r1_tarski @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.49/0.75      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.49/0.75  thf('24', plain,
% 0.49/0.75      (![X0 : $i, X1 : $i]:
% 0.49/0.75         ((r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 0.49/0.75      inference('sup-', [status(thm)], ['22', '23'])).
% 0.49/0.75  thf('25', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X0))),
% 0.49/0.75      inference('sup-', [status(thm)], ['21', '24'])).
% 0.49/0.75  thf('26', plain,
% 0.49/0.75      (![X3 : $i, X5 : $i]:
% 0.49/0.75         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.49/0.75      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.75  thf('27', plain,
% 0.49/0.75      (![X0 : $i]:
% 0.49/0.75         ((k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.49/0.75      inference('sup-', [status(thm)], ['25', '26'])).
% 0.49/0.75  thf('28', plain,
% 0.49/0.75      (![X18 : $i, X19 : $i]:
% 0.49/0.75         ((k6_subset_1 @ X18 @ (k6_subset_1 @ X18 @ X19))
% 0.49/0.75           = (k3_xboole_0 @ X18 @ X19))),
% 0.49/0.75      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.49/0.75  thf('29', plain,
% 0.49/0.75      (![X18 : $i, X19 : $i]:
% 0.49/0.75         ((k6_subset_1 @ X18 @ (k6_subset_1 @ X18 @ X19))
% 0.49/0.75           = (k3_xboole_0 @ X18 @ X19))),
% 0.49/0.75      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.49/0.75  thf('30', plain,
% 0.49/0.75      (![X0 : $i, X1 : $i]:
% 0.49/0.75         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.49/0.75           = (k3_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 0.49/0.75      inference('sup+', [status(thm)], ['28', '29'])).
% 0.49/0.75  thf('31', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.49/0.75      inference('simplify', [status(thm)], ['20'])).
% 0.49/0.75  thf('32', plain,
% 0.49/0.75      (![X3 : $i, X5 : $i]:
% 0.49/0.75         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.49/0.75      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.75  thf('33', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.75      inference('sup-', [status(thm)], ['31', '32'])).
% 0.49/0.75  thf('34', plain,
% 0.49/0.75      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.75      inference('demod', [status(thm)], ['27', '30', '33'])).
% 0.49/0.75  thf('35', plain,
% 0.49/0.75      (![X18 : $i, X19 : $i]:
% 0.49/0.75         ((k6_subset_1 @ X18 @ (k6_subset_1 @ X18 @ X19))
% 0.49/0.75           = (k3_xboole_0 @ X18 @ X19))),
% 0.49/0.75      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.49/0.75  thf('36', plain,
% 0.49/0.75      (![X3 : $i, X4 : $i]:
% 0.49/0.75         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.49/0.75      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.49/0.75  thf('37', plain,
% 0.49/0.75      (![X20 : $i, X21 : $i]:
% 0.49/0.75         ((k6_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))),
% 0.49/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.49/0.75  thf('38', plain,
% 0.49/0.75      (![X3 : $i, X4 : $i]:
% 0.49/0.75         ((r1_tarski @ X3 @ X4) | ((k6_subset_1 @ X3 @ X4) != (k1_xboole_0)))),
% 0.49/0.75      inference('demod', [status(thm)], ['36', '37'])).
% 0.49/0.75  thf('39', plain,
% 0.49/0.75      (![X0 : $i, X1 : $i]:
% 0.49/0.75         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.49/0.75          | (r1_tarski @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 0.49/0.75      inference('sup-', [status(thm)], ['35', '38'])).
% 0.49/0.75  thf('40', plain,
% 0.49/0.75      (![X0 : $i]:
% 0.49/0.75         (((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.75          | (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ k1_xboole_0)))),
% 0.49/0.75      inference('sup-', [status(thm)], ['34', '39'])).
% 0.49/0.75  thf('41', plain,
% 0.49/0.75      (![X0 : $i]: (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ k1_xboole_0))),
% 0.49/0.75      inference('simplify', [status(thm)], ['40'])).
% 0.49/0.75  thf(t36_xboole_1, axiom,
% 0.49/0.75    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.49/0.75  thf('42', plain,
% 0.49/0.75      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.49/0.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.49/0.75  thf('43', plain,
% 0.49/0.75      (![X20 : $i, X21 : $i]:
% 0.49/0.75         ((k6_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))),
% 0.49/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.49/0.75  thf('44', plain,
% 0.49/0.75      (![X14 : $i, X15 : $i]: (r1_tarski @ (k6_subset_1 @ X14 @ X15) @ X14)),
% 0.49/0.75      inference('demod', [status(thm)], ['42', '43'])).
% 0.49/0.75  thf('45', plain,
% 0.49/0.75      (![X0 : $i, X2 : $i]:
% 0.49/0.75         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.49/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.49/0.75  thf('46', plain,
% 0.49/0.75      (![X0 : $i, X1 : $i]:
% 0.49/0.75         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.49/0.75          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 0.49/0.75      inference('sup-', [status(thm)], ['44', '45'])).
% 0.49/0.75  thf('47', plain, (![X0 : $i]: ((X0) = (k6_subset_1 @ X0 @ k1_xboole_0))),
% 0.49/0.75      inference('sup-', [status(thm)], ['41', '46'])).
% 0.49/0.75  thf('48', plain,
% 0.49/0.75      (![X0 : $i]:
% 0.49/0.75         ((k10_relat_1 @ sk_C @ 
% 0.49/0.75           (k6_subset_1 @ X0 @ (k6_subset_1 @ sk_A @ sk_B)))
% 0.49/0.75           = (k10_relat_1 @ sk_C @ X0))),
% 0.49/0.75      inference('demod', [status(thm)], ['19', '47'])).
% 0.49/0.75  thf('49', plain,
% 0.49/0.75      (((k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.49/0.75         = (k10_relat_1 @ sk_C @ sk_A))),
% 0.49/0.75      inference('sup+', [status(thm)], ['4', '48'])).
% 0.49/0.75  thf('50', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.49/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.75  thf('51', plain,
% 0.49/0.75      (![X18 : $i, X19 : $i]:
% 0.49/0.75         ((k6_subset_1 @ X18 @ (k6_subset_1 @ X18 @ X19))
% 0.49/0.75           = (k3_xboole_0 @ X18 @ X19))),
% 0.49/0.75      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.49/0.75  thf('52', plain,
% 0.49/0.75      (![X14 : $i, X15 : $i]: (r1_tarski @ (k6_subset_1 @ X14 @ X15) @ X14)),
% 0.49/0.75      inference('demod', [status(thm)], ['42', '43'])).
% 0.49/0.75  thf('53', plain,
% 0.49/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.49/0.75      inference('sup+', [status(thm)], ['51', '52'])).
% 0.49/0.75  thf(t12_xboole_1, axiom,
% 0.49/0.75    (![A:$i,B:$i]:
% 0.49/0.75     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.49/0.75  thf('54', plain,
% 0.49/0.75      (![X9 : $i, X10 : $i]:
% 0.49/0.75         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.49/0.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.49/0.75  thf('55', plain,
% 0.49/0.75      (![X0 : $i, X1 : $i]:
% 0.49/0.75         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.49/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.49/0.75  thf(t11_xboole_1, axiom,
% 0.49/0.75    (![A:$i,B:$i,C:$i]:
% 0.49/0.75     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.49/0.75  thf('56', plain,
% 0.49/0.75      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.49/0.75         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 0.49/0.75      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.49/0.75  thf('57', plain,
% 0.49/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.75         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 0.49/0.75      inference('sup-', [status(thm)], ['55', '56'])).
% 0.49/0.75  thf('58', plain,
% 0.49/0.75      (![X0 : $i]:
% 0.49/0.75         (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k2_relat_1 @ sk_C))),
% 0.49/0.75      inference('sup-', [status(thm)], ['50', '57'])).
% 0.49/0.75  thf(t147_funct_1, axiom,
% 0.49/0.75    (![A:$i,B:$i]:
% 0.49/0.75     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.75       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.49/0.75         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.49/0.75  thf('59', plain,
% 0.49/0.75      (![X27 : $i, X28 : $i]:
% 0.49/0.75         (~ (r1_tarski @ X27 @ (k2_relat_1 @ X28))
% 0.49/0.75          | ((k9_relat_1 @ X28 @ (k10_relat_1 @ X28 @ X27)) = (X27))
% 0.49/0.75          | ~ (v1_funct_1 @ X28)
% 0.49/0.75          | ~ (v1_relat_1 @ X28))),
% 0.49/0.75      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.49/0.75  thf('60', plain,
% 0.49/0.75      (![X0 : $i]:
% 0.49/0.75         (~ (v1_relat_1 @ sk_C)
% 0.49/0.75          | ~ (v1_funct_1 @ sk_C)
% 0.49/0.75          | ((k9_relat_1 @ sk_C @ 
% 0.49/0.75              (k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ X0)))
% 0.49/0.75              = (k3_xboole_0 @ sk_A @ X0)))),
% 0.49/0.75      inference('sup-', [status(thm)], ['58', '59'])).
% 0.49/0.75  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.75  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.75  thf('63', plain,
% 0.49/0.75      (![X0 : $i]:
% 0.49/0.75         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ X0)))
% 0.49/0.75           = (k3_xboole_0 @ sk_A @ X0))),
% 0.49/0.75      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.49/0.75  thf('64', plain,
% 0.49/0.75      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.49/0.75         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.49/0.75      inference('sup+', [status(thm)], ['49', '63'])).
% 0.49/0.75  thf('65', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.49/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.75  thf('66', plain,
% 0.49/0.75      (![X27 : $i, X28 : $i]:
% 0.49/0.75         (~ (r1_tarski @ X27 @ (k2_relat_1 @ X28))
% 0.49/0.75          | ((k9_relat_1 @ X28 @ (k10_relat_1 @ X28 @ X27)) = (X27))
% 0.49/0.75          | ~ (v1_funct_1 @ X28)
% 0.49/0.75          | ~ (v1_relat_1 @ X28))),
% 0.49/0.75      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.49/0.75  thf('67', plain,
% 0.49/0.75      ((~ (v1_relat_1 @ sk_C)
% 0.49/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.75        | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.49/0.75      inference('sup-', [status(thm)], ['65', '66'])).
% 0.49/0.75  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.75  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.75  thf('70', plain,
% 0.49/0.75      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.49/0.75      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.49/0.75  thf('71', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.49/0.75      inference('sup+', [status(thm)], ['64', '70'])).
% 0.49/0.75  thf('72', plain,
% 0.49/0.75      (![X18 : $i, X19 : $i]:
% 0.49/0.75         ((k6_subset_1 @ X18 @ (k6_subset_1 @ X18 @ X19))
% 0.49/0.75           = (k3_xboole_0 @ X18 @ X19))),
% 0.49/0.75      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.49/0.75  thf(t38_xboole_1, axiom,
% 0.49/0.75    (![A:$i,B:$i]:
% 0.49/0.75     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.49/0.75       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.49/0.75  thf('73', plain,
% 0.49/0.75      (![X16 : $i, X17 : $i]:
% 0.49/0.75         (((X16) = (k1_xboole_0))
% 0.49/0.75          | ~ (r1_tarski @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.49/0.75      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.49/0.75  thf('74', plain,
% 0.49/0.75      (![X20 : $i, X21 : $i]:
% 0.49/0.75         ((k6_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))),
% 0.49/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.49/0.75  thf('75', plain,
% 0.49/0.75      (![X16 : $i, X17 : $i]:
% 0.49/0.75         (((X16) = (k1_xboole_0))
% 0.49/0.75          | ~ (r1_tarski @ X16 @ (k6_subset_1 @ X17 @ X16)))),
% 0.49/0.75      inference('demod', [status(thm)], ['73', '74'])).
% 0.49/0.75  thf('76', plain,
% 0.49/0.75      (![X0 : $i, X1 : $i]:
% 0.49/0.75         (~ (r1_tarski @ (k6_subset_1 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.49/0.75          | ((k6_subset_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.49/0.75      inference('sup-', [status(thm)], ['72', '75'])).
% 0.49/0.75  thf('77', plain,
% 0.49/0.75      ((~ (r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ sk_A)
% 0.49/0.75        | ((k6_subset_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.75      inference('sup-', [status(thm)], ['71', '76'])).
% 0.49/0.75  thf('78', plain,
% 0.49/0.75      (![X14 : $i, X15 : $i]: (r1_tarski @ (k6_subset_1 @ X14 @ X15) @ X14)),
% 0.49/0.75      inference('demod', [status(thm)], ['42', '43'])).
% 0.49/0.75  thf('79', plain, (((k6_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.49/0.75      inference('demod', [status(thm)], ['77', '78'])).
% 0.49/0.75  thf('80', plain,
% 0.49/0.75      (![X3 : $i, X4 : $i]:
% 0.49/0.75         ((r1_tarski @ X3 @ X4) | ((k6_subset_1 @ X3 @ X4) != (k1_xboole_0)))),
% 0.49/0.75      inference('demod', [status(thm)], ['36', '37'])).
% 0.49/0.75  thf('81', plain,
% 0.49/0.75      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.49/0.75      inference('sup-', [status(thm)], ['79', '80'])).
% 0.49/0.75  thf('82', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.49/0.75      inference('simplify', [status(thm)], ['81'])).
% 0.49/0.75  thf('83', plain, ($false), inference('demod', [status(thm)], ['0', '82'])).
% 0.49/0.75  
% 0.49/0.75  % SZS output end Refutation
% 0.49/0.75  
% 0.58/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
