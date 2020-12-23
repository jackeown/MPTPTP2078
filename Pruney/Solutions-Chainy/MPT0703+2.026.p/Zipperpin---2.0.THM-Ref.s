%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6dbUVSyIGu

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:52 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 188 expanded)
%              Number of leaves         :   22 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  643 (1662 expanded)
%              Number of equality atoms :   31 (  64 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X1 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) )
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('24',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k10_relat_1 @ X23 @ ( k6_subset_1 @ X24 @ X25 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X23 @ X24 ) @ ( k10_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
        = ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('28',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k6_subset_1 @ X3 @ X5 ) @ X4 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('31',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X26 @ ( k2_relat_1 @ X27 ) )
      | ( ( k9_relat_1 @ X27 @ ( k10_relat_1 @ X27 @ X26 ) )
        = X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
        = ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
      = ( k6_subset_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) )
      = ( k6_subset_1 @ sk_A @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['25','35'])).

thf('37',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k10_relat_1 @ X23 @ ( k6_subset_1 @ X24 @ X25 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X23 @ X24 ) @ ( k10_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('39',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,
    ( ( k2_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k2_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['37','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) @ X0 ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('52',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) )
      | ( X0
        = ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
      = ( k6_subset_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('56',plain,
    ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['36','56','57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('62',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('63',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('64',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['4','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6dbUVSyIGu
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:31:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.97/1.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.97/1.16  % Solved by: fo/fo7.sh
% 0.97/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.97/1.16  % done 1789 iterations in 0.680s
% 0.97/1.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.97/1.16  % SZS output start Refutation
% 0.97/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.97/1.16  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.97/1.16  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.97/1.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.97/1.16  thf(sk_C_type, type, sk_C: $i).
% 0.97/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.97/1.16  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.97/1.16  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.97/1.16  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.97/1.16  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.97/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.97/1.16  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.97/1.16  thf(t158_funct_1, conjecture,
% 0.97/1.16    (![A:$i,B:$i,C:$i]:
% 0.97/1.16     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.97/1.16       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.97/1.16           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.97/1.16         ( r1_tarski @ A @ B ) ) ))).
% 0.97/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.97/1.16    (~( ![A:$i,B:$i,C:$i]:
% 0.97/1.16        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.97/1.16          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.97/1.16              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.97/1.16            ( r1_tarski @ A @ B ) ) ) )),
% 0.97/1.16    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.97/1.16  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf(d10_xboole_0, axiom,
% 0.97/1.16    (![A:$i,B:$i]:
% 0.97/1.16     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.97/1.16  thf('1', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.97/1.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.97/1.16  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.97/1.16      inference('simplify', [status(thm)], ['1'])).
% 0.97/1.16  thf(t12_xboole_1, axiom,
% 0.97/1.16    (![A:$i,B:$i]:
% 0.97/1.16     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.97/1.16  thf('3', plain,
% 0.97/1.16      (![X9 : $i, X10 : $i]:
% 0.97/1.16         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.97/1.16      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.97/1.16  thf('4', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.97/1.16      inference('sup-', [status(thm)], ['2', '3'])).
% 0.97/1.16  thf('5', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.97/1.16      inference('simplify', [status(thm)], ['1'])).
% 0.97/1.16  thf(t11_xboole_1, axiom,
% 0.97/1.16    (![A:$i,B:$i,C:$i]:
% 0.97/1.16     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.97/1.16  thf('6', plain,
% 0.97/1.16      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.97/1.16         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 0.97/1.16      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.97/1.16  thf('7', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.97/1.16      inference('sup-', [status(thm)], ['5', '6'])).
% 0.97/1.16  thf('8', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('9', plain,
% 0.97/1.16      (![X9 : $i, X10 : $i]:
% 0.97/1.16         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.97/1.16      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.97/1.16  thf('10', plain,
% 0.97/1.16      (((k2_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.97/1.16      inference('sup-', [status(thm)], ['8', '9'])).
% 0.97/1.16  thf('11', plain,
% 0.97/1.16      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.97/1.16         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 0.97/1.16      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.97/1.16  thf('12', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0) | (r1_tarski @ sk_A @ X0))),
% 0.97/1.16      inference('sup-', [status(thm)], ['10', '11'])).
% 0.97/1.16  thf('13', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))),
% 0.97/1.16      inference('sup-', [status(thm)], ['7', '12'])).
% 0.97/1.16  thf(t43_xboole_1, axiom,
% 0.97/1.16    (![A:$i,B:$i,C:$i]:
% 0.97/1.16     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.97/1.16       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.97/1.16  thf('14', plain,
% 0.97/1.16      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.97/1.16         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.97/1.16          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.97/1.16      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.97/1.16  thf(redefinition_k6_subset_1, axiom,
% 0.97/1.16    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.97/1.16  thf('15', plain,
% 0.97/1.16      (![X21 : $i, X22 : $i]:
% 0.97/1.16         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 0.97/1.16      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.97/1.16  thf('16', plain,
% 0.97/1.16      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.97/1.16         ((r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15)
% 0.97/1.16          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.97/1.16      inference('demod', [status(thm)], ['14', '15'])).
% 0.97/1.16  thf('17', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         (r1_tarski @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)) @ X0)),
% 0.97/1.16      inference('sup-', [status(thm)], ['13', '16'])).
% 0.97/1.16  thf('18', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.97/1.16      inference('sup-', [status(thm)], ['5', '6'])).
% 0.97/1.16  thf('19', plain,
% 0.97/1.16      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.97/1.16         ((r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15)
% 0.97/1.16          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.97/1.16      inference('demod', [status(thm)], ['14', '15'])).
% 0.97/1.16  thf('20', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X1 @ X1) @ X0)),
% 0.97/1.16      inference('sup-', [status(thm)], ['18', '19'])).
% 0.97/1.16  thf('21', plain,
% 0.97/1.16      (![X0 : $i, X2 : $i]:
% 0.97/1.16         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.97/1.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.97/1.16  thf('22', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]:
% 0.97/1.16         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X1 @ X1))
% 0.97/1.16          | ((X0) = (k6_subset_1 @ X1 @ X1)))),
% 0.97/1.16      inference('sup-', [status(thm)], ['20', '21'])).
% 0.97/1.16  thf('23', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         ((k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)) = (k6_subset_1 @ X0 @ X0))),
% 0.97/1.16      inference('sup-', [status(thm)], ['17', '22'])).
% 0.97/1.16  thf(t138_funct_1, axiom,
% 0.97/1.16    (![A:$i,B:$i,C:$i]:
% 0.97/1.16     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.97/1.16       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.97/1.16         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.97/1.16  thf('24', plain,
% 0.97/1.16      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.97/1.16         (((k10_relat_1 @ X23 @ (k6_subset_1 @ X24 @ X25))
% 0.97/1.16            = (k6_subset_1 @ (k10_relat_1 @ X23 @ X24) @ 
% 0.97/1.16               (k10_relat_1 @ X23 @ X25)))
% 0.97/1.16          | ~ (v1_funct_1 @ X23)
% 0.97/1.16          | ~ (v1_relat_1 @ X23))),
% 0.97/1.16      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.97/1.16  thf('25', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]:
% 0.97/1.16         (((k10_relat_1 @ X1 @ (k6_subset_1 @ X0 @ X0))
% 0.97/1.16            = (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))
% 0.97/1.16          | ~ (v1_relat_1 @ X1)
% 0.97/1.16          | ~ (v1_funct_1 @ X1))),
% 0.97/1.16      inference('sup+', [status(thm)], ['23', '24'])).
% 0.97/1.16  thf('26', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf(t109_xboole_1, axiom,
% 0.97/1.16    (![A:$i,B:$i,C:$i]:
% 0.97/1.16     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.97/1.16  thf('27', plain,
% 0.97/1.16      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.97/1.16         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k4_xboole_0 @ X3 @ X5) @ X4))),
% 0.97/1.16      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.97/1.16  thf('28', plain,
% 0.97/1.16      (![X21 : $i, X22 : $i]:
% 0.97/1.16         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 0.97/1.16      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.97/1.16  thf('29', plain,
% 0.97/1.16      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.97/1.16         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k6_subset_1 @ X3 @ X5) @ X4))),
% 0.97/1.16      inference('demod', [status(thm)], ['27', '28'])).
% 0.97/1.16  thf('30', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_C))),
% 0.97/1.16      inference('sup-', [status(thm)], ['26', '29'])).
% 0.97/1.16  thf(t147_funct_1, axiom,
% 0.97/1.16    (![A:$i,B:$i]:
% 0.97/1.16     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.97/1.16       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.97/1.16         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.97/1.16  thf('31', plain,
% 0.97/1.16      (![X26 : $i, X27 : $i]:
% 0.97/1.16         (~ (r1_tarski @ X26 @ (k2_relat_1 @ X27))
% 0.97/1.16          | ((k9_relat_1 @ X27 @ (k10_relat_1 @ X27 @ X26)) = (X26))
% 0.97/1.16          | ~ (v1_funct_1 @ X27)
% 0.97/1.16          | ~ (v1_relat_1 @ X27))),
% 0.97/1.16      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.97/1.16  thf('32', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         (~ (v1_relat_1 @ sk_C)
% 0.97/1.16          | ~ (v1_funct_1 @ sk_C)
% 0.97/1.16          | ((k9_relat_1 @ sk_C @ 
% 0.97/1.16              (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.97/1.16              = (k6_subset_1 @ sk_A @ X0)))),
% 0.97/1.16      inference('sup-', [status(thm)], ['30', '31'])).
% 0.97/1.16  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('35', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.97/1.16           = (k6_subset_1 @ sk_A @ X0))),
% 0.97/1.16      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.97/1.16  thf('36', plain,
% 0.97/1.16      ((((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))
% 0.97/1.16          = (k6_subset_1 @ sk_A @ sk_A))
% 0.97/1.16        | ~ (v1_funct_1 @ sk_C)
% 0.97/1.16        | ~ (v1_relat_1 @ sk_C))),
% 0.97/1.16      inference('sup+', [status(thm)], ['25', '35'])).
% 0.97/1.16  thf('37', plain,
% 0.97/1.16      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.97/1.16         (((k10_relat_1 @ X23 @ (k6_subset_1 @ X24 @ X25))
% 0.97/1.16            = (k6_subset_1 @ (k10_relat_1 @ X23 @ X24) @ 
% 0.97/1.16               (k10_relat_1 @ X23 @ X25)))
% 0.97/1.16          | ~ (v1_funct_1 @ X23)
% 0.97/1.16          | ~ (v1_relat_1 @ X23))),
% 0.97/1.16      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.97/1.16  thf('38', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.97/1.16      inference('sup-', [status(thm)], ['5', '6'])).
% 0.97/1.16  thf('39', plain,
% 0.97/1.16      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('40', plain,
% 0.97/1.16      (![X9 : $i, X10 : $i]:
% 0.97/1.16         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.97/1.16      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.97/1.16  thf('41', plain,
% 0.97/1.16      (((k2_xboole_0 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.97/1.16         (k10_relat_1 @ sk_C @ sk_B)) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.97/1.16      inference('sup-', [status(thm)], ['39', '40'])).
% 0.97/1.16  thf('42', plain,
% 0.97/1.16      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.97/1.16         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 0.97/1.16      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.97/1.16  thf('43', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         (~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_B) @ X0)
% 0.97/1.16          | (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ X0))),
% 0.97/1.16      inference('sup-', [status(thm)], ['41', '42'])).
% 0.97/1.16  thf('44', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.97/1.16          (k2_xboole_0 @ (k10_relat_1 @ sk_C @ sk_B) @ X0))),
% 0.97/1.16      inference('sup-', [status(thm)], ['38', '43'])).
% 0.97/1.16  thf('45', plain,
% 0.97/1.16      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.97/1.16         ((r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15)
% 0.97/1.16          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.97/1.16      inference('demod', [status(thm)], ['14', '15'])).
% 0.97/1.16  thf('46', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         (r1_tarski @ 
% 0.97/1.16          (k6_subset_1 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.97/1.16           (k10_relat_1 @ sk_C @ sk_B)) @ 
% 0.97/1.16          X0)),
% 0.97/1.16      inference('sup-', [status(thm)], ['44', '45'])).
% 0.97/1.16  thf('47', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         ((r1_tarski @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) @ X0)
% 0.97/1.16          | ~ (v1_relat_1 @ sk_C)
% 0.97/1.16          | ~ (v1_funct_1 @ sk_C))),
% 0.97/1.16      inference('sup+', [status(thm)], ['37', '46'])).
% 0.97/1.16  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('50', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         (r1_tarski @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) @ X0)),
% 0.97/1.16      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.97/1.16  thf('51', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         (r1_tarski @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)) @ X0)),
% 0.97/1.16      inference('sup-', [status(thm)], ['13', '16'])).
% 0.97/1.16  thf('52', plain,
% 0.97/1.16      (![X0 : $i, X2 : $i]:
% 0.97/1.16         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.97/1.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.97/1.16  thf('53', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         (~ (r1_tarski @ X0 @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))
% 0.97/1.16          | ((X0) = (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C))))),
% 0.97/1.16      inference('sup-', [status(thm)], ['51', '52'])).
% 0.97/1.16  thf('54', plain,
% 0.97/1.16      (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B))
% 0.97/1.16         = (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))),
% 0.97/1.16      inference('sup-', [status(thm)], ['50', '53'])).
% 0.97/1.16  thf('55', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.97/1.16           = (k6_subset_1 @ sk_A @ X0))),
% 0.97/1.16      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.97/1.16  thf('56', plain,
% 0.97/1.16      (((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))
% 0.97/1.16         = (k6_subset_1 @ sk_A @ sk_B))),
% 0.97/1.16      inference('sup+', [status(thm)], ['54', '55'])).
% 0.97/1.16  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('59', plain,
% 0.97/1.16      (((k6_subset_1 @ sk_A @ sk_B) = (k6_subset_1 @ sk_A @ sk_A))),
% 0.97/1.16      inference('demod', [status(thm)], ['36', '56', '57', '58'])).
% 0.97/1.16  thf('60', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X1 @ X1) @ X0)),
% 0.97/1.16      inference('sup-', [status(thm)], ['18', '19'])).
% 0.97/1.16  thf('61', plain,
% 0.97/1.16      (![X0 : $i]: (r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ X0)),
% 0.97/1.16      inference('sup+', [status(thm)], ['59', '60'])).
% 0.97/1.16  thf(t44_xboole_1, axiom,
% 0.97/1.16    (![A:$i,B:$i,C:$i]:
% 0.97/1.16     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.97/1.16       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.97/1.16  thf('62', plain,
% 0.97/1.16      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.97/1.16         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 0.97/1.16          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 0.97/1.16      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.97/1.16  thf('63', plain,
% 0.97/1.16      (![X21 : $i, X22 : $i]:
% 0.97/1.16         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 0.97/1.16      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.97/1.16  thf('64', plain,
% 0.97/1.16      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.97/1.16         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 0.97/1.16          | ~ (r1_tarski @ (k6_subset_1 @ X16 @ X17) @ X18))),
% 0.97/1.16      inference('demod', [status(thm)], ['62', '63'])).
% 0.97/1.16  thf('65', plain,
% 0.97/1.16      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ X0))),
% 0.97/1.16      inference('sup-', [status(thm)], ['61', '64'])).
% 0.97/1.16  thf('66', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.97/1.16      inference('sup+', [status(thm)], ['4', '65'])).
% 0.97/1.16  thf('67', plain, ($false), inference('demod', [status(thm)], ['0', '66'])).
% 0.97/1.16  
% 0.97/1.16  % SZS output end Refutation
% 0.97/1.16  
% 1.02/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
