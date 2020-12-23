%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hbOID5ZLsr

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:50 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 287 expanded)
%              Number of leaves         :   26 ( 104 expanded)
%              Depth                    :   23
%              Number of atoms          :  923 (2391 expanded)
%              Number of equality atoms :   76 ( 192 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ ( k6_subset_1 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('5',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k6_subset_1 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ X22 @ ( k6_subset_1 @ X23 @ X24 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X22 @ X23 ) @ ( k10_relat_1 @ X22 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('11',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['9','10'])).

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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ X22 @ ( k6_subset_1 @ X23 @ X24 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X22 @ X23 ) @ ( k10_relat_1 @ X22 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ ( k6_subset_1 @ sk_A @ sk_B ) @ X0 ) )
        = ( k6_subset_1 @ k1_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('19',plain,(
    ! [X15: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ ( k6_subset_1 @ sk_A @ sk_B ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k6_subset_1 @ sk_A @ sk_B ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ ( k6_subset_1 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['24','33'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('35',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X25 @ ( k2_relat_1 @ X26 ) )
      | ( ( k9_relat_1 @ X26 @ ( k10_relat_1 @ X26 @ X25 ) )
        = X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_A ) ) )
        = ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_A ) ) )
      = ( k3_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k6_subset_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['23','39'])).

thf('41',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ X22 @ ( k6_subset_1 @ X23 @ X24 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X22 @ X23 ) @ ( k10_relat_1 @ X22 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('42',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ ( k6_subset_1 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('43',plain,(
    ! [X15: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ ( k6_subset_1 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k6_subset_1 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('53',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('54',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('55',plain,(
    ! [X9: $i] :
      ( ( k6_subset_1 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k6_subset_1 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ X22 @ ( k6_subset_1 @ X23 @ X24 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X22 @ X23 ) @ ( k10_relat_1 @ X22 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('61',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ sk_A ) @ X0 ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['59','69'])).

thf('71',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k6_subset_1 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('72',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ k1_xboole_0 @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['41','72'])).

thf('74',plain,(
    ! [X15: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('78',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('79',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X25 @ ( k2_relat_1 @ X26 ) )
      | ( ( k9_relat_1 @ X26 @ ( k10_relat_1 @ X26 @ X25 ) )
        = X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('86',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ ( k6_subset_1 @ ( k6_subset_1 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('92',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k6_subset_1 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','97'])).

thf('99',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k6_subset_1 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('101',plain,
    ( ( k6_subset_1 @ ( k6_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X9: $i] :
      ( ( k6_subset_1 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('103',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k6_subset_1 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('105',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['0','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hbOID5ZLsr
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:36:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 499 iterations in 0.147s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.43/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.61  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.43/0.61  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.43/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.61  thf(t158_funct_1, conjecture,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.43/0.61       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.43/0.61           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.43/0.61         ( r1_tarski @ A @ B ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.61        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.43/0.61          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.43/0.61              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.43/0.61            ( r1_tarski @ A @ B ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.43/0.61  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t48_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      (![X13 : $i, X14 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.43/0.61           = (k3_xboole_0 @ X13 @ X14))),
% 0.43/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.61  thf(redefinition_k6_subset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      (![X13 : $i, X14 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X13 @ (k6_subset_1 @ X13 @ X14))
% 0.43/0.61           = (k3_xboole_0 @ X13 @ X14))),
% 0.43/0.61      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(l32_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      (![X2 : $i, X4 : $i]:
% 0.43/0.61         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.43/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (![X2 : $i, X4 : $i]:
% 0.43/0.61         (((k6_subset_1 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.43/0.61      inference('demod', [status(thm)], ['6', '7'])).
% 0.43/0.61  thf('9', plain,
% 0.43/0.61      (((k6_subset_1 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.43/0.61         (k10_relat_1 @ sk_C @ sk_B)) = (k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['5', '8'])).
% 0.43/0.61  thf(t138_funct_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.43/0.61       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.43/0.61         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.43/0.61         (((k10_relat_1 @ X22 @ (k6_subset_1 @ X23 @ X24))
% 0.43/0.61            = (k6_subset_1 @ (k10_relat_1 @ X22 @ X23) @ 
% 0.43/0.61               (k10_relat_1 @ X22 @ X24)))
% 0.43/0.61          | ~ (v1_funct_1 @ X22)
% 0.43/0.61          | ~ (v1_relat_1 @ X22))),
% 0.43/0.61      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      ((((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.43/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.43/0.61        | ~ (v1_funct_1 @ sk_C))),
% 0.43/0.61      inference('sup+', [status(thm)], ['9', '10'])).
% 0.43/0.61  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('14', plain,
% 0.43/0.61      (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.43/0.61         (((k10_relat_1 @ X22 @ (k6_subset_1 @ X23 @ X24))
% 0.43/0.61            = (k6_subset_1 @ (k10_relat_1 @ X22 @ X23) @ 
% 0.43/0.61               (k10_relat_1 @ X22 @ X24)))
% 0.43/0.61          | ~ (v1_funct_1 @ X22)
% 0.43/0.61          | ~ (v1_relat_1 @ X22))),
% 0.43/0.61      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.43/0.61  thf('16', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k10_relat_1 @ sk_C @ 
% 0.43/0.61            (k6_subset_1 @ (k6_subset_1 @ sk_A @ sk_B) @ X0))
% 0.43/0.61            = (k6_subset_1 @ k1_xboole_0 @ (k10_relat_1 @ sk_C @ X0)))
% 0.43/0.61          | ~ (v1_relat_1 @ sk_C)
% 0.43/0.61          | ~ (v1_funct_1 @ sk_C))),
% 0.43/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.43/0.61  thf(t4_boole, axiom,
% 0.43/0.61    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.43/0.61  thf('17', plain,
% 0.43/0.61      (![X15 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 0.43/0.61      inference('cnf', [status(esa)], [t4_boole])).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.43/0.61  thf('19', plain,
% 0.43/0.61      (![X15 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.43/0.61  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((k10_relat_1 @ sk_C @ 
% 0.43/0.61           (k6_subset_1 @ (k6_subset_1 @ sk_A @ sk_B) @ X0)) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['16', '19', '20', '21'])).
% 0.43/0.61  thf('23', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((k10_relat_1 @ sk_C @ 
% 0.43/0.61           (k3_xboole_0 @ (k6_subset_1 @ sk_A @ sk_B) @ X0)) = (k1_xboole_0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['4', '22'])).
% 0.43/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.43/0.61  thf('24', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      (![X13 : $i, X14 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X13 @ (k6_subset_1 @ X13 @ X14))
% 0.43/0.61           = (k3_xboole_0 @ X13 @ X14))),
% 0.43/0.61      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.43/0.61  thf('26', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t10_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.43/0.61  thf('27', plain,
% 0.43/0.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.43/0.61         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ X5 @ (k2_xboole_0 @ X7 @ X6)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_C)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.43/0.61  thf(t43_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.43/0.61       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.43/0.61  thf('29', plain,
% 0.43/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.43/0.61         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.43/0.61          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.43/0.61  thf('30', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.43/0.61  thf('31', plain,
% 0.43/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.43/0.61         ((r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X12)
% 0.43/0.61          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.43/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.43/0.61  thf('32', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_C))),
% 0.43/0.61      inference('sup-', [status(thm)], ['28', '31'])).
% 0.43/0.61  thf('33', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k2_relat_1 @ sk_C))),
% 0.43/0.61      inference('sup+', [status(thm)], ['25', '32'])).
% 0.43/0.61  thf('34', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.43/0.61      inference('sup+', [status(thm)], ['24', '33'])).
% 0.43/0.61  thf(t147_funct_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.61       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.43/0.61         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.43/0.61  thf('35', plain,
% 0.43/0.61      (![X25 : $i, X26 : $i]:
% 0.43/0.61         (~ (r1_tarski @ X25 @ (k2_relat_1 @ X26))
% 0.43/0.61          | ((k9_relat_1 @ X26 @ (k10_relat_1 @ X26 @ X25)) = (X25))
% 0.43/0.61          | ~ (v1_funct_1 @ X26)
% 0.43/0.61          | ~ (v1_relat_1 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.43/0.61  thf('36', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ sk_C)
% 0.43/0.61          | ~ (v1_funct_1 @ sk_C)
% 0.43/0.61          | ((k9_relat_1 @ sk_C @ 
% 0.43/0.61              (k10_relat_1 @ sk_C @ (k3_xboole_0 @ X0 @ sk_A)))
% 0.43/0.61              = (k3_xboole_0 @ X0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.43/0.61  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('39', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k3_xboole_0 @ X0 @ sk_A)))
% 0.43/0.61           = (k3_xboole_0 @ X0 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.43/0.61  thf('40', plain,
% 0.43/0.61      (((k9_relat_1 @ sk_C @ k1_xboole_0)
% 0.43/0.61         = (k3_xboole_0 @ (k6_subset_1 @ sk_A @ sk_B) @ sk_A))),
% 0.43/0.61      inference('sup+', [status(thm)], ['23', '39'])).
% 0.43/0.61  thf('41', plain,
% 0.43/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.43/0.61         (((k10_relat_1 @ X22 @ (k6_subset_1 @ X23 @ X24))
% 0.43/0.61            = (k6_subset_1 @ (k10_relat_1 @ X22 @ X23) @ 
% 0.43/0.61               (k10_relat_1 @ X22 @ X24)))
% 0.43/0.61          | ~ (v1_funct_1 @ X22)
% 0.43/0.61          | ~ (v1_relat_1 @ X22))),
% 0.43/0.61      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.43/0.61  thf('42', plain,
% 0.43/0.61      (![X13 : $i, X14 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X13 @ (k6_subset_1 @ X13 @ X14))
% 0.43/0.61           = (k3_xboole_0 @ X13 @ X14))),
% 0.43/0.61      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.43/0.61  thf('43', plain,
% 0.43/0.61      (![X15 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.43/0.61  thf('44', plain,
% 0.43/0.61      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.43/0.61  thf('45', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.61  thf('46', plain,
% 0.43/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['44', '45'])).
% 0.43/0.61  thf('47', plain,
% 0.43/0.61      (![X13 : $i, X14 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X13 @ (k6_subset_1 @ X13 @ X14))
% 0.43/0.61           = (k3_xboole_0 @ X13 @ X14))),
% 0.43/0.61      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.43/0.61  thf('48', plain,
% 0.43/0.61      (![X2 : $i, X3 : $i]:
% 0.43/0.61         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.43/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.43/0.61  thf('49', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.43/0.61  thf('50', plain,
% 0.43/0.61      (![X2 : $i, X3 : $i]:
% 0.43/0.61         ((r1_tarski @ X2 @ X3) | ((k6_subset_1 @ X2 @ X3) != (k1_xboole_0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['48', '49'])).
% 0.43/0.61  thf('51', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.43/0.61          | (r1_tarski @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['47', '50'])).
% 0.43/0.61  thf('52', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k1_xboole_0) != (k1_xboole_0))
% 0.43/0.61          | (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['46', '51'])).
% 0.43/0.61  thf(t3_boole, axiom,
% 0.43/0.61    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.43/0.61  thf('53', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.43/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.61  thf('54', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.43/0.61  thf('55', plain, (![X9 : $i]: ((k6_subset_1 @ X9 @ k1_xboole_0) = (X9))),
% 0.43/0.61      inference('demod', [status(thm)], ['53', '54'])).
% 0.43/0.61  thf('56', plain,
% 0.43/0.61      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ X0 @ X0))),
% 0.43/0.61      inference('demod', [status(thm)], ['52', '55'])).
% 0.43/0.61  thf('57', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.43/0.61      inference('simplify', [status(thm)], ['56'])).
% 0.43/0.61  thf('58', plain,
% 0.43/0.61      (![X2 : $i, X4 : $i]:
% 0.43/0.61         (((k6_subset_1 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.43/0.61      inference('demod', [status(thm)], ['6', '7'])).
% 0.43/0.61  thf('59', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['57', '58'])).
% 0.43/0.61  thf('60', plain,
% 0.43/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.43/0.61         (((k10_relat_1 @ X22 @ (k6_subset_1 @ X23 @ X24))
% 0.43/0.61            = (k6_subset_1 @ (k10_relat_1 @ X22 @ X23) @ 
% 0.43/0.61               (k10_relat_1 @ X22 @ X24)))
% 0.43/0.61          | ~ (v1_funct_1 @ X22)
% 0.43/0.61          | ~ (v1_relat_1 @ X22))),
% 0.43/0.61      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.43/0.61  thf('61', plain,
% 0.43/0.61      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('62', plain,
% 0.43/0.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.43/0.61         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ X5 @ (k2_xboole_0 @ X7 @ X6)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.43/0.61  thf('63', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.43/0.61          (k2_xboole_0 @ X0 @ (k10_relat_1 @ sk_C @ sk_B)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['61', '62'])).
% 0.43/0.61  thf('64', plain,
% 0.43/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.43/0.61         ((r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X12)
% 0.43/0.61          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.43/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.43/0.61  thf('65', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (r1_tarski @ (k6_subset_1 @ (k10_relat_1 @ sk_C @ sk_A) @ X0) @ 
% 0.43/0.61          (k10_relat_1 @ sk_C @ sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['63', '64'])).
% 0.43/0.61  thf('66', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((r1_tarski @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)) @ 
% 0.43/0.61           (k10_relat_1 @ sk_C @ sk_B))
% 0.43/0.61          | ~ (v1_relat_1 @ sk_C)
% 0.43/0.61          | ~ (v1_funct_1 @ sk_C))),
% 0.43/0.61      inference('sup+', [status(thm)], ['60', '65'])).
% 0.43/0.61  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('69', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (r1_tarski @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)) @ 
% 0.43/0.61          (k10_relat_1 @ sk_C @ sk_B))),
% 0.43/0.61      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.43/0.61  thf('70', plain,
% 0.43/0.61      ((r1_tarski @ (k10_relat_1 @ sk_C @ k1_xboole_0) @ 
% 0.43/0.61        (k10_relat_1 @ sk_C @ sk_B))),
% 0.43/0.61      inference('sup+', [status(thm)], ['59', '69'])).
% 0.43/0.61  thf('71', plain,
% 0.43/0.61      (![X2 : $i, X4 : $i]:
% 0.43/0.61         (((k6_subset_1 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.43/0.61      inference('demod', [status(thm)], ['6', '7'])).
% 0.43/0.61  thf('72', plain,
% 0.43/0.61      (((k6_subset_1 @ (k10_relat_1 @ sk_C @ k1_xboole_0) @ 
% 0.43/0.61         (k10_relat_1 @ sk_C @ sk_B)) = (k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['70', '71'])).
% 0.43/0.61  thf('73', plain,
% 0.43/0.61      ((((k10_relat_1 @ sk_C @ (k6_subset_1 @ k1_xboole_0 @ sk_B))
% 0.43/0.61          = (k1_xboole_0))
% 0.43/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.43/0.61        | ~ (v1_funct_1 @ sk_C))),
% 0.43/0.61      inference('sup+', [status(thm)], ['41', '72'])).
% 0.43/0.61  thf('74', plain,
% 0.43/0.61      (![X15 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.43/0.61  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('77', plain, (((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 0.43/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.43/0.61  thf('78', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.43/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.43/0.61  thf('79', plain,
% 0.43/0.61      (![X25 : $i, X26 : $i]:
% 0.43/0.61         (~ (r1_tarski @ X25 @ (k2_relat_1 @ X26))
% 0.43/0.61          | ((k9_relat_1 @ X26 @ (k10_relat_1 @ X26 @ X25)) = (X25))
% 0.43/0.61          | ~ (v1_funct_1 @ X26)
% 0.43/0.61          | ~ (v1_relat_1 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.43/0.61  thf('80', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X0)
% 0.43/0.61          | ~ (v1_funct_1 @ X0)
% 0.43/0.61          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 0.43/0.61              = (k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['78', '79'])).
% 0.43/0.61  thf('81', plain,
% 0.43/0.61      ((((k9_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))
% 0.43/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.43/0.61        | ~ (v1_relat_1 @ sk_C))),
% 0.43/0.61      inference('sup+', [status(thm)], ['77', '80'])).
% 0.43/0.61  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('83', plain, ((v1_relat_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('84', plain, (((k9_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.43/0.61  thf('85', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.61  thf('86', plain,
% 0.43/0.61      (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ (k6_subset_1 @ sk_A @ sk_B)))),
% 0.43/0.61      inference('demod', [status(thm)], ['40', '84', '85'])).
% 0.43/0.61  thf('87', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.61  thf('88', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.43/0.61          | (r1_tarski @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['47', '50'])).
% 0.43/0.61  thf('89', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.43/0.61          | (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['87', '88'])).
% 0.43/0.61  thf('90', plain,
% 0.43/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.43/0.61        | (r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ 
% 0.43/0.61           (k6_subset_1 @ (k6_subset_1 @ sk_A @ sk_B) @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['86', '89'])).
% 0.43/0.61  thf('91', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.43/0.61      inference('simplify', [status(thm)], ['56'])).
% 0.43/0.61  thf('92', plain,
% 0.43/0.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.43/0.61         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ X5 @ (k2_xboole_0 @ X7 @ X6)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.43/0.61  thf('93', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['91', '92'])).
% 0.43/0.61  thf('94', plain,
% 0.43/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.43/0.61         ((r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X12)
% 0.43/0.61          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.43/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.43/0.61  thf('95', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 0.43/0.61      inference('sup-', [status(thm)], ['93', '94'])).
% 0.43/0.61  thf('96', plain,
% 0.43/0.61      (![X2 : $i, X4 : $i]:
% 0.43/0.61         (((k6_subset_1 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.43/0.61      inference('demod', [status(thm)], ['6', '7'])).
% 0.43/0.61  thf('97', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((k6_subset_1 @ (k6_subset_1 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['95', '96'])).
% 0.43/0.61  thf('98', plain,
% 0.43/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.43/0.61        | (r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['90', '97'])).
% 0.43/0.61  thf('99', plain, ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ k1_xboole_0)),
% 0.43/0.61      inference('simplify', [status(thm)], ['98'])).
% 0.43/0.61  thf('100', plain,
% 0.43/0.61      (![X2 : $i, X4 : $i]:
% 0.43/0.61         (((k6_subset_1 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.43/0.61      inference('demod', [status(thm)], ['6', '7'])).
% 0.43/0.61  thf('101', plain,
% 0.43/0.61      (((k6_subset_1 @ (k6_subset_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.43/0.61         = (k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['99', '100'])).
% 0.43/0.61  thf('102', plain, (![X9 : $i]: ((k6_subset_1 @ X9 @ k1_xboole_0) = (X9))),
% 0.43/0.61      inference('demod', [status(thm)], ['53', '54'])).
% 0.43/0.61  thf('103', plain, (((k6_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['101', '102'])).
% 0.43/0.61  thf('104', plain,
% 0.43/0.61      (![X2 : $i, X3 : $i]:
% 0.43/0.61         ((r1_tarski @ X2 @ X3) | ((k6_subset_1 @ X2 @ X3) != (k1_xboole_0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['48', '49'])).
% 0.43/0.61  thf('105', plain,
% 0.43/0.61      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['103', '104'])).
% 0.43/0.61  thf('106', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.43/0.61      inference('simplify', [status(thm)], ['105'])).
% 0.43/0.61  thf('107', plain, ($false), inference('demod', [status(thm)], ['0', '106'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
