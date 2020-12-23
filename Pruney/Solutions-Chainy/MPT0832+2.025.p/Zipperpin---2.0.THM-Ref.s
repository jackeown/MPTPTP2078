%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.McIqKGxeL6

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:31 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 577 expanded)
%              Number of leaves         :   26 ( 190 expanded)
%              Depth                    :   22
%              Number of atoms          :  870 (4666 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t35_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( m1_subset_1 @ ( k6_relset_1 @ C @ A @ B @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
       => ( m1_subset_1 @ ( k6_relset_1 @ C @ A @ B @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k6_relset_1 @ sk_C @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k6_relset_1 @ A @ B @ C @ D )
        = ( k8_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( ( k6_relset_1 @ X23 @ X24 @ X21 @ X22 )
        = ( k8_relat_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k8_relat_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X12 @ X13 ) ) @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ( ( k8_relat_1 @ X17 @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X14 @ X15 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['7','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X14 @ X15 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X14 @ X15 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X3 )
      | ~ ( r1_tarski @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( v5_relat_1 @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_D ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
      | ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ( ( k8_relat_1 @ X17 @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) )
      | ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) )
        = ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('62',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_D ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['60','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','69'])).

thf('71',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ( ( k8_relat_1 @ X17 @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_D ) ) )
      | ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_D ) ) )
        = ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_D ) ) )
      = ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) )
        = ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ sk_D ) ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['14','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('77',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ sk_D )
      = ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X12 @ X13 ) ) @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('84',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X26 )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['4','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.McIqKGxeL6
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.65/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.65/0.84  % Solved by: fo/fo7.sh
% 0.65/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.84  % done 729 iterations in 0.426s
% 0.65/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.65/0.84  % SZS output start Refutation
% 0.65/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.65/0.84  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.65/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.65/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.65/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.65/0.84  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.65/0.84  thf(sk_D_type, type, sk_D: $i).
% 0.65/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.65/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.65/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.65/0.84  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 0.65/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.65/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.84  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.65/0.84  thf(t35_relset_1, conjecture,
% 0.65/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.84     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.65/0.84       ( m1_subset_1 @
% 0.65/0.84         ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 0.65/0.84         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.65/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.84    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.84        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.65/0.84          ( m1_subset_1 @
% 0.65/0.84            ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 0.65/0.84            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )),
% 0.65/0.84    inference('cnf.neg', [status(esa)], [t35_relset_1])).
% 0.65/0.84  thf('0', plain,
% 0.65/0.84      (~ (m1_subset_1 @ (k6_relset_1 @ sk_C @ sk_A @ sk_B @ sk_D) @ 
% 0.65/0.84          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('1', plain,
% 0.65/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf(redefinition_k6_relset_1, axiom,
% 0.65/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.84     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.84       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 0.65/0.84  thf('2', plain,
% 0.65/0.84      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.65/0.84         (((k6_relset_1 @ X23 @ X24 @ X21 @ X22) = (k8_relat_1 @ X21 @ X22))
% 0.65/0.84          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.65/0.84      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 0.65/0.84  thf('3', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         ((k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 0.65/0.84      inference('sup-', [status(thm)], ['1', '2'])).
% 0.65/0.84  thf('4', plain,
% 0.65/0.84      (~ (m1_subset_1 @ (k8_relat_1 @ sk_B @ sk_D) @ 
% 0.65/0.84          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.65/0.84      inference('demod', [status(thm)], ['0', '3'])).
% 0.65/0.84  thf(t116_relat_1, axiom,
% 0.65/0.84    (![A:$i,B:$i]:
% 0.65/0.84     ( ( v1_relat_1 @ B ) =>
% 0.65/0.84       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.65/0.84  thf('5', plain,
% 0.65/0.84      (![X12 : $i, X13 : $i]:
% 0.65/0.84         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X12 @ X13)) @ X12)
% 0.65/0.84          | ~ (v1_relat_1 @ X13))),
% 0.65/0.84      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.65/0.84  thf(t125_relat_1, axiom,
% 0.65/0.84    (![A:$i,B:$i]:
% 0.65/0.84     ( ( v1_relat_1 @ B ) =>
% 0.65/0.84       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.65/0.84         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.65/0.84  thf('6', plain,
% 0.65/0.84      (![X16 : $i, X17 : $i]:
% 0.65/0.84         (~ (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 0.65/0.84          | ((k8_relat_1 @ X17 @ X16) = (X16))
% 0.65/0.84          | ~ (v1_relat_1 @ X16))),
% 0.65/0.84      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.65/0.84  thf('7', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ X1)
% 0.65/0.84          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1))
% 0.65/0.84          | ((k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ X1))
% 0.65/0.84              = (k8_relat_1 @ X0 @ X1)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['5', '6'])).
% 0.65/0.84  thf(t117_relat_1, axiom,
% 0.65/0.84    (![A:$i,B:$i]:
% 0.65/0.84     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.65/0.84  thf('8', plain,
% 0.65/0.84      (![X14 : $i, X15 : $i]:
% 0.65/0.84         ((r1_tarski @ (k8_relat_1 @ X14 @ X15) @ X15) | ~ (v1_relat_1 @ X15))),
% 0.65/0.84      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.65/0.84  thf(t3_subset, axiom,
% 0.65/0.84    (![A:$i,B:$i]:
% 0.65/0.84     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.65/0.84  thf('9', plain,
% 0.65/0.84      (![X3 : $i, X5 : $i]:
% 0.65/0.84         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.65/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.65/0.84  thf('10', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ X0)
% 0.65/0.84          | (m1_subset_1 @ (k8_relat_1 @ X1 @ X0) @ (k1_zfmisc_1 @ X0)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['8', '9'])).
% 0.65/0.84  thf(cc2_relat_1, axiom,
% 0.65/0.84    (![A:$i]:
% 0.65/0.84     ( ( v1_relat_1 @ A ) =>
% 0.65/0.84       ( ![B:$i]:
% 0.65/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.65/0.84  thf('11', plain,
% 0.65/0.84      (![X6 : $i, X7 : $i]:
% 0.65/0.84         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.65/0.84          | (v1_relat_1 @ X6)
% 0.65/0.84          | ~ (v1_relat_1 @ X7))),
% 0.65/0.84      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.65/0.84  thf('12', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ X0)
% 0.65/0.84          | ~ (v1_relat_1 @ X0)
% 0.65/0.84          | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['10', '11'])).
% 0.65/0.84  thf('13', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.65/0.84      inference('simplify', [status(thm)], ['12'])).
% 0.65/0.84  thf('14', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (((k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ X1)) = (k8_relat_1 @ X0 @ X1))
% 0.65/0.84          | ~ (v1_relat_1 @ X1))),
% 0.65/0.84      inference('clc', [status(thm)], ['7', '13'])).
% 0.65/0.84  thf('15', plain,
% 0.65/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('16', plain,
% 0.65/0.84      (![X3 : $i, X4 : $i]:
% 0.65/0.84         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.65/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.65/0.84  thf('17', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_C @ sk_A))),
% 0.65/0.84      inference('sup-', [status(thm)], ['15', '16'])).
% 0.65/0.84  thf('18', plain,
% 0.65/0.84      (![X14 : $i, X15 : $i]:
% 0.65/0.84         ((r1_tarski @ (k8_relat_1 @ X14 @ X15) @ X15) | ~ (v1_relat_1 @ X15))),
% 0.65/0.84      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.65/0.84  thf('19', plain,
% 0.65/0.84      (![X14 : $i, X15 : $i]:
% 0.65/0.84         ((r1_tarski @ (k8_relat_1 @ X14 @ X15) @ X15) | ~ (v1_relat_1 @ X15))),
% 0.65/0.84      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.65/0.84  thf(t1_xboole_1, axiom,
% 0.65/0.84    (![A:$i,B:$i,C:$i]:
% 0.65/0.84     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.65/0.84       ( r1_tarski @ A @ C ) ))).
% 0.65/0.84  thf('20', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.84         (~ (r1_tarski @ X0 @ X1)
% 0.65/0.84          | ~ (r1_tarski @ X1 @ X2)
% 0.65/0.84          | (r1_tarski @ X0 @ X2))),
% 0.65/0.84      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.65/0.84  thf('21', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ X0)
% 0.65/0.84          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.65/0.84          | ~ (r1_tarski @ X0 @ X2))),
% 0.65/0.84      inference('sup-', [status(thm)], ['19', '20'])).
% 0.65/0.84  thf('22', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ X0)
% 0.65/0.84          | (r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ X0)
% 0.65/0.84          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['18', '21'])).
% 0.65/0.84  thf('23', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.65/0.84      inference('simplify', [status(thm)], ['12'])).
% 0.65/0.84  thf('24', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.84         ((r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ X0)
% 0.65/0.84          | ~ (v1_relat_1 @ X0))),
% 0.65/0.84      inference('clc', [status(thm)], ['22', '23'])).
% 0.65/0.84  thf('25', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.84         (~ (r1_tarski @ X0 @ X1)
% 0.65/0.84          | ~ (r1_tarski @ X1 @ X2)
% 0.65/0.84          | (r1_tarski @ X0 @ X2))),
% 0.65/0.84      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.65/0.84  thf('26', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ X0)
% 0.65/0.84          | (r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ X3)
% 0.65/0.84          | ~ (r1_tarski @ X0 @ X3))),
% 0.65/0.84      inference('sup-', [status(thm)], ['24', '25'])).
% 0.65/0.84  thf('27', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((r1_tarski @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_D)) @ 
% 0.65/0.84           (k2_zfmisc_1 @ sk_C @ sk_A))
% 0.65/0.84          | ~ (v1_relat_1 @ sk_D))),
% 0.65/0.84      inference('sup-', [status(thm)], ['17', '26'])).
% 0.65/0.84  thf('28', plain,
% 0.65/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('29', plain,
% 0.65/0.84      (![X6 : $i, X7 : $i]:
% 0.65/0.84         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.65/0.84          | (v1_relat_1 @ X6)
% 0.65/0.84          | ~ (v1_relat_1 @ X7))),
% 0.65/0.84      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.65/0.84  thf('30', plain,
% 0.65/0.84      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.65/0.84      inference('sup-', [status(thm)], ['28', '29'])).
% 0.65/0.84  thf(fc6_relat_1, axiom,
% 0.65/0.84    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.65/0.84  thf('31', plain,
% 0.65/0.84      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.65/0.84  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.65/0.84      inference('demod', [status(thm)], ['30', '31'])).
% 0.65/0.84  thf('33', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (r1_tarski @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_D)) @ 
% 0.65/0.84          (k2_zfmisc_1 @ sk_C @ sk_A))),
% 0.65/0.84      inference('demod', [status(thm)], ['27', '32'])).
% 0.65/0.84  thf('34', plain,
% 0.65/0.84      (![X3 : $i, X5 : $i]:
% 0.65/0.84         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.65/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.65/0.84  thf('35', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (m1_subset_1 @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_D)) @ 
% 0.65/0.84          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['33', '34'])).
% 0.65/0.84  thf(cc2_relset_1, axiom,
% 0.65/0.84    (![A:$i,B:$i,C:$i]:
% 0.65/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.84       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.65/0.84  thf('36', plain,
% 0.65/0.84      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.65/0.84         ((v5_relat_1 @ X18 @ X20)
% 0.65/0.84          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.65/0.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.65/0.84  thf('37', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (v5_relat_1 @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_A)),
% 0.65/0.84      inference('sup-', [status(thm)], ['35', '36'])).
% 0.65/0.84  thf(d19_relat_1, axiom,
% 0.65/0.84    (![A:$i,B:$i]:
% 0.65/0.84     ( ( v1_relat_1 @ B ) =>
% 0.65/0.84       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.65/0.84  thf('38', plain,
% 0.65/0.84      (![X8 : $i, X9 : $i]:
% 0.65/0.84         (~ (v5_relat_1 @ X8 @ X9)
% 0.65/0.84          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.65/0.84          | ~ (v1_relat_1 @ X8))),
% 0.65/0.84      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.65/0.84  thf('39', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_D)))
% 0.65/0.84          | (r1_tarski @ 
% 0.65/0.84             (k2_relat_1 @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_D))) @ sk_A))),
% 0.65/0.84      inference('sup-', [status(thm)], ['37', '38'])).
% 0.65/0.84  thf('40', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_C @ sk_A))),
% 0.65/0.84      inference('sup-', [status(thm)], ['15', '16'])).
% 0.65/0.84  thf('41', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ X0)
% 0.65/0.84          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.65/0.84          | ~ (r1_tarski @ X0 @ X2))),
% 0.65/0.84      inference('sup-', [status(thm)], ['19', '20'])).
% 0.65/0.84  thf('42', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_D) @ (k2_zfmisc_1 @ sk_C @ sk_A))
% 0.65/0.84          | ~ (v1_relat_1 @ sk_D))),
% 0.65/0.84      inference('sup-', [status(thm)], ['40', '41'])).
% 0.65/0.84  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 0.65/0.84      inference('demod', [status(thm)], ['30', '31'])).
% 0.65/0.84  thf('44', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         (r1_tarski @ (k8_relat_1 @ X0 @ sk_D) @ (k2_zfmisc_1 @ sk_C @ sk_A))),
% 0.65/0.84      inference('demod', [status(thm)], ['42', '43'])).
% 0.65/0.84  thf('45', plain,
% 0.65/0.84      (![X3 : $i, X5 : $i]:
% 0.65/0.84         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.65/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.65/0.84  thf('46', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.65/0.84          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['44', '45'])).
% 0.65/0.84  thf('47', plain,
% 0.65/0.84      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.65/0.84         ((v5_relat_1 @ X18 @ X20)
% 0.65/0.84          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.65/0.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.65/0.84  thf('48', plain,
% 0.65/0.84      (![X0 : $i]: (v5_relat_1 @ (k8_relat_1 @ X0 @ sk_D) @ sk_A)),
% 0.65/0.84      inference('sup-', [status(thm)], ['46', '47'])).
% 0.65/0.84  thf('49', plain,
% 0.65/0.84      (![X8 : $i, X9 : $i]:
% 0.65/0.84         (~ (v5_relat_1 @ X8 @ X9)
% 0.65/0.84          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.65/0.84          | ~ (v1_relat_1 @ X8))),
% 0.65/0.84      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.65/0.84  thf('50', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))
% 0.65/0.84          | (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_A))),
% 0.65/0.84      inference('sup-', [status(thm)], ['48', '49'])).
% 0.65/0.84  thf('51', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.65/0.84          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['44', '45'])).
% 0.65/0.84  thf('52', plain,
% 0.65/0.84      (![X6 : $i, X7 : $i]:
% 0.65/0.84         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.65/0.84          | (v1_relat_1 @ X6)
% 0.65/0.84          | ~ (v1_relat_1 @ X7))),
% 0.65/0.84      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.65/0.84  thf('53', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A))
% 0.65/0.84          | (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['51', '52'])).
% 0.65/0.84  thf('54', plain,
% 0.65/0.84      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.65/0.84  thf('55', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))),
% 0.65/0.84      inference('demod', [status(thm)], ['53', '54'])).
% 0.65/0.84  thf('56', plain,
% 0.65/0.84      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_A)),
% 0.65/0.84      inference('demod', [status(thm)], ['50', '55'])).
% 0.65/0.84  thf('57', plain,
% 0.65/0.84      (![X16 : $i, X17 : $i]:
% 0.65/0.84         (~ (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 0.65/0.84          | ((k8_relat_1 @ X17 @ X16) = (X16))
% 0.65/0.84          | ~ (v1_relat_1 @ X16))),
% 0.65/0.84      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.65/0.84  thf('58', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))
% 0.65/0.84          | ((k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 0.65/0.84              = (k8_relat_1 @ X0 @ sk_D)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['56', '57'])).
% 0.65/0.84  thf('59', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))),
% 0.65/0.84      inference('demod', [status(thm)], ['53', '54'])).
% 0.65/0.84  thf('60', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         ((k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 0.65/0.84           = (k8_relat_1 @ X0 @ sk_D))),
% 0.65/0.84      inference('demod', [status(thm)], ['58', '59'])).
% 0.65/0.84  thf('61', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.84         ((r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ X0)
% 0.65/0.84          | ~ (v1_relat_1 @ X0))),
% 0.65/0.84      inference('clc', [status(thm)], ['22', '23'])).
% 0.65/0.84  thf('62', plain,
% 0.65/0.84      (![X3 : $i, X5 : $i]:
% 0.65/0.84         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.65/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.65/0.84  thf('63', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ X0)
% 0.65/0.84          | (m1_subset_1 @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.65/0.84             (k1_zfmisc_1 @ X0)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['61', '62'])).
% 0.65/0.84  thf('64', plain,
% 0.65/0.84      (![X6 : $i, X7 : $i]:
% 0.65/0.84         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.65/0.84          | (v1_relat_1 @ X6)
% 0.65/0.84          | ~ (v1_relat_1 @ X7))),
% 0.65/0.84      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.65/0.84  thf('65', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ X0)
% 0.65/0.84          | ~ (v1_relat_1 @ X0)
% 0.65/0.84          | (v1_relat_1 @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))))),
% 0.65/0.84      inference('sup-', [status(thm)], ['63', '64'])).
% 0.65/0.84  thf('66', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.84         ((v1_relat_1 @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)))
% 0.65/0.84          | ~ (v1_relat_1 @ X0))),
% 0.65/0.84      inference('simplify', [status(thm)], ['65'])).
% 0.65/0.84  thf('67', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_D)))
% 0.65/0.84          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['60', '66'])).
% 0.65/0.84  thf('68', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))),
% 0.65/0.84      inference('demod', [status(thm)], ['53', '54'])).
% 0.65/0.84  thf('69', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 0.65/0.84      inference('demod', [status(thm)], ['67', '68'])).
% 0.65/0.84  thf('70', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (r1_tarski @ 
% 0.65/0.84          (k2_relat_1 @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_D))) @ sk_A)),
% 0.65/0.84      inference('demod', [status(thm)], ['39', '69'])).
% 0.65/0.84  thf('71', plain,
% 0.65/0.84      (![X16 : $i, X17 : $i]:
% 0.65/0.84         (~ (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 0.65/0.84          | ((k8_relat_1 @ X17 @ X16) = (X16))
% 0.65/0.84          | ~ (v1_relat_1 @ X16))),
% 0.65/0.84      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.65/0.84  thf('72', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_D)))
% 0.65/0.84          | ((k8_relat_1 @ sk_A @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_D)))
% 0.65/0.84              = (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_D))))),
% 0.65/0.84      inference('sup-', [status(thm)], ['70', '71'])).
% 0.65/0.84  thf('73', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 0.65/0.84      inference('demod', [status(thm)], ['67', '68'])).
% 0.65/0.84  thf('74', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k8_relat_1 @ sk_A @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_D)))
% 0.65/0.84           = (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 0.65/0.84      inference('demod', [status(thm)], ['72', '73'])).
% 0.65/0.84  thf('75', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         (((k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 0.65/0.84            = (k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ sk_D)))
% 0.65/0.84          | ~ (v1_relat_1 @ sk_D))),
% 0.65/0.84      inference('sup+', [status(thm)], ['14', '74'])).
% 0.65/0.84  thf('76', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         ((k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 0.65/0.84           = (k8_relat_1 @ X0 @ sk_D))),
% 0.65/0.84      inference('demod', [status(thm)], ['58', '59'])).
% 0.65/0.84  thf('77', plain, ((v1_relat_1 @ sk_D)),
% 0.65/0.84      inference('demod', [status(thm)], ['30', '31'])).
% 0.65/0.84  thf('78', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         ((k8_relat_1 @ X0 @ sk_D)
% 0.65/0.84           = (k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ sk_D)))),
% 0.65/0.84      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.65/0.84  thf('79', plain,
% 0.65/0.84      (![X12 : $i, X13 : $i]:
% 0.65/0.84         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X12 @ X13)) @ X12)
% 0.65/0.84          | ~ (v1_relat_1 @ X13))),
% 0.65/0.84      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.65/0.84  thf('80', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X0)
% 0.65/0.84          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['78', '79'])).
% 0.65/0.84  thf('81', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))),
% 0.65/0.84      inference('demod', [status(thm)], ['53', '54'])).
% 0.65/0.84  thf('82', plain,
% 0.65/0.84      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X0)),
% 0.65/0.84      inference('demod', [status(thm)], ['80', '81'])).
% 0.65/0.84  thf('83', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.65/0.84          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['44', '45'])).
% 0.65/0.84  thf(t14_relset_1, axiom,
% 0.65/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.84     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.65/0.84       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.65/0.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.65/0.84  thf('84', plain,
% 0.65/0.84      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.65/0.84         (~ (r1_tarski @ (k2_relat_1 @ X25) @ X26)
% 0.65/0.84          | (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.65/0.84          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.65/0.84      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.65/0.84  thf('85', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.65/0.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.65/0.84          | ~ (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X1))),
% 0.65/0.84      inference('sup-', [status(thm)], ['83', '84'])).
% 0.65/0.84  thf('86', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.65/0.84          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['82', '85'])).
% 0.65/0.84  thf('87', plain, ($false), inference('demod', [status(thm)], ['4', '86'])).
% 0.65/0.84  
% 0.65/0.84  % SZS output end Refutation
% 0.65/0.84  
% 0.65/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
