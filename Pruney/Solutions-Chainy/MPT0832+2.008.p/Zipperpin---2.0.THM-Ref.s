%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.naSQhZH366

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:29 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :  126 (1119 expanded)
%              Number of leaves         :   28 ( 349 expanded)
%              Depth                    :   33
%              Number of atoms          : 1025 (10706 expanded)
%              Number of equality atoms :   36 ( 209 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( ( k6_relset_1 @ X25 @ X26 @ X23 @ X24 )
        = ( k8_relat_1 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X4 @ X5 ) ) @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ( ( k8_relat_1 @ X9 @ X8 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(t118_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) ) @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t118_relat_1])).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ( ( k8_relat_1 @ X9 @ X8 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf('18',plain,(
    ! [X10: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X10 ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X4 @ X5 ) ) @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf(t130_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( ( k8_relat_1 @ X11 @ ( k8_relat_1 @ X12 @ X13 ) )
        = ( k8_relat_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t130_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ ( k8_relat_1 @ X0 @ X2 ) )
        = ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
        = ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ X0 )
        = ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
        = ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ( ( k8_relat_1 @ X9 @ X8 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k8_relat_1 @ sk_A @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('40',plain,
    ( ( k8_relat_1 @ sk_A @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) ) @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t118_relat_1])).

thf('42',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('44',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ( ( k8_relat_1 @ X9 @ X8 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k8_relat_1 @ ( k2_relat_1 @ sk_D ) @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('48',plain,
    ( ( k8_relat_1 @ ( k2_relat_1 @ sk_D ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X4 @ X5 ) ) @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf(t131_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ) )).

thf('50',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k8_relat_1 @ X14 @ X16 ) @ ( k8_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t131_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ X2 ) @ ( k8_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_D ) @ X0 ) ) @ sk_D ) @ sk_D )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_D ) @ X0 ) ) @ sk_D ) @ sk_D )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_D ) @ sk_D )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['27','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_D ) @ sk_D )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_D ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_D ) @ sk_D ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_D ) @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['25','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_D ) @ sk_D ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ( ( r1_tarski @ A @ D )
       => ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('65',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r1_tarski @ X31 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t4_relset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('73',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ( ( k8_relat_1 @ X9 @ X8 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) )
      | ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) )
        = ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ ( k8_relat_1 @ X0 @ sk_D ) )
        = ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('83',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ ( k8_relat_1 @ X0 @ sk_D ) )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ sk_D ) )
        = ( k8_relat_1 @ X0 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['17','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ sk_D ) )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X4 @ X5 ) ) @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('93',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ X28 )
      | ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['4','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.naSQhZH366
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.00/1.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.00/1.20  % Solved by: fo/fo7.sh
% 1.00/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.20  % done 1032 iterations in 0.739s
% 1.00/1.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.00/1.20  % SZS output start Refutation
% 1.00/1.20  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 1.00/1.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.00/1.20  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.00/1.20  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.00/1.20  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.00/1.20  thf(sk_D_type, type, sk_D: $i).
% 1.00/1.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.00/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.00/1.20  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 1.00/1.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.00/1.20  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.00/1.20  thf(sk_C_type, type, sk_C: $i).
% 1.00/1.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.00/1.20  thf(t35_relset_1, conjecture,
% 1.00/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.00/1.20     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.00/1.20       ( m1_subset_1 @
% 1.00/1.20         ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 1.00/1.20         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 1.00/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.20    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.00/1.20        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.00/1.20          ( m1_subset_1 @
% 1.00/1.20            ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 1.00/1.20            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )),
% 1.00/1.20    inference('cnf.neg', [status(esa)], [t35_relset_1])).
% 1.00/1.20  thf('0', plain,
% 1.00/1.20      (~ (m1_subset_1 @ (k6_relset_1 @ sk_C @ sk_A @ sk_B @ sk_D) @ 
% 1.00/1.20          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('1', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf(redefinition_k6_relset_1, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.00/1.20     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.00/1.20       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 1.00/1.20  thf('2', plain,
% 1.00/1.20      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.00/1.20         (((k6_relset_1 @ X25 @ X26 @ X23 @ X24) = (k8_relat_1 @ X23 @ X24))
% 1.00/1.20          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.00/1.20      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 1.00/1.20  thf('3', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 1.00/1.20      inference('sup-', [status(thm)], ['1', '2'])).
% 1.00/1.20  thf('4', plain,
% 1.00/1.20      (~ (m1_subset_1 @ (k8_relat_1 @ sk_B @ sk_D) @ 
% 1.00/1.20          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.00/1.20      inference('demod', [status(thm)], ['0', '3'])).
% 1.00/1.20  thf(t116_relat_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( v1_relat_1 @ B ) =>
% 1.00/1.20       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 1.00/1.20  thf('5', plain,
% 1.00/1.20      (![X4 : $i, X5 : $i]:
% 1.00/1.20         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X4 @ X5)) @ X4)
% 1.00/1.20          | ~ (v1_relat_1 @ X5))),
% 1.00/1.20      inference('cnf', [status(esa)], [t116_relat_1])).
% 1.00/1.20  thf(t125_relat_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( v1_relat_1 @ B ) =>
% 1.00/1.20       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.00/1.20         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 1.00/1.20  thf('6', plain,
% 1.00/1.20      (![X8 : $i, X9 : $i]:
% 1.00/1.20         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 1.00/1.20          | ((k8_relat_1 @ X9 @ X8) = (X8))
% 1.00/1.20          | ~ (v1_relat_1 @ X8))),
% 1.00/1.20      inference('cnf', [status(esa)], [t125_relat_1])).
% 1.00/1.20  thf('7', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (~ (v1_relat_1 @ X1)
% 1.00/1.20          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1))
% 1.00/1.20          | ((k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ X1))
% 1.00/1.20              = (k8_relat_1 @ X0 @ X1)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['5', '6'])).
% 1.00/1.20  thf(dt_k8_relat_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 1.00/1.20  thf('8', plain,
% 1.00/1.20      (![X2 : $i, X3 : $i]:
% 1.00/1.20         ((v1_relat_1 @ (k8_relat_1 @ X2 @ X3)) | ~ (v1_relat_1 @ X3))),
% 1.00/1.20      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 1.00/1.20  thf('9', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (((k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ X1)) = (k8_relat_1 @ X0 @ X1))
% 1.00/1.20          | ~ (v1_relat_1 @ X1))),
% 1.00/1.20      inference('clc', [status(thm)], ['7', '8'])).
% 1.00/1.20  thf(t118_relat_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( v1_relat_1 @ B ) =>
% 1.00/1.20       ( r1_tarski @
% 1.00/1.20         ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ))).
% 1.00/1.20  thf('10', plain,
% 1.00/1.20      (![X6 : $i, X7 : $i]:
% 1.00/1.20         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X6 @ X7)) @ 
% 1.00/1.20           (k2_relat_1 @ X7))
% 1.00/1.20          | ~ (v1_relat_1 @ X7))),
% 1.00/1.20      inference('cnf', [status(esa)], [t118_relat_1])).
% 1.00/1.20  thf('11', plain,
% 1.00/1.20      (![X8 : $i, X9 : $i]:
% 1.00/1.20         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 1.00/1.20          | ((k8_relat_1 @ X9 @ X8) = (X8))
% 1.00/1.20          | ~ (v1_relat_1 @ X8))),
% 1.00/1.20      inference('cnf', [status(esa)], [t125_relat_1])).
% 1.00/1.20  thf('12', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (~ (v1_relat_1 @ X0)
% 1.00/1.20          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 1.00/1.20          | ((k8_relat_1 @ (k2_relat_1 @ X0) @ (k8_relat_1 @ X1 @ X0))
% 1.00/1.20              = (k8_relat_1 @ X1 @ X0)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['10', '11'])).
% 1.00/1.20  thf('13', plain,
% 1.00/1.20      (![X2 : $i, X3 : $i]:
% 1.00/1.20         ((v1_relat_1 @ (k8_relat_1 @ X2 @ X3)) | ~ (v1_relat_1 @ X3))),
% 1.00/1.20      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 1.00/1.20  thf('14', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (((k8_relat_1 @ (k2_relat_1 @ X0) @ (k8_relat_1 @ X1 @ X0))
% 1.00/1.20            = (k8_relat_1 @ X1 @ X0))
% 1.00/1.20          | ~ (v1_relat_1 @ X0))),
% 1.00/1.20      inference('clc', [status(thm)], ['12', '13'])).
% 1.00/1.20  thf('15', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (((k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ 
% 1.00/1.20            (k8_relat_1 @ X1 @ X0))
% 1.00/1.20            = (k8_relat_1 @ X1 @ (k8_relat_1 @ X1 @ X0)))
% 1.00/1.20          | ~ (v1_relat_1 @ X0)
% 1.00/1.20          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 1.00/1.20      inference('sup+', [status(thm)], ['9', '14'])).
% 1.00/1.20  thf('16', plain,
% 1.00/1.20      (![X2 : $i, X3 : $i]:
% 1.00/1.20         ((v1_relat_1 @ (k8_relat_1 @ X2 @ X3)) | ~ (v1_relat_1 @ X3))),
% 1.00/1.20      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 1.00/1.20  thf('17', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (~ (v1_relat_1 @ X0)
% 1.00/1.20          | ((k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ 
% 1.00/1.20              (k8_relat_1 @ X1 @ X0))
% 1.00/1.20              = (k8_relat_1 @ X1 @ (k8_relat_1 @ X1 @ X0))))),
% 1.00/1.20      inference('clc', [status(thm)], ['15', '16'])).
% 1.00/1.20  thf(t126_relat_1, axiom,
% 1.00/1.20    (![A:$i]:
% 1.00/1.20     ( ( v1_relat_1 @ A ) =>
% 1.00/1.20       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 1.00/1.20  thf('18', plain,
% 1.00/1.20      (![X10 : $i]:
% 1.00/1.20         (((k8_relat_1 @ (k2_relat_1 @ X10) @ X10) = (X10))
% 1.00/1.20          | ~ (v1_relat_1 @ X10))),
% 1.00/1.20      inference('cnf', [status(esa)], [t126_relat_1])).
% 1.00/1.20  thf('19', plain,
% 1.00/1.20      (![X4 : $i, X5 : $i]:
% 1.00/1.20         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X4 @ X5)) @ X4)
% 1.00/1.20          | ~ (v1_relat_1 @ X5))),
% 1.00/1.20      inference('cnf', [status(esa)], [t116_relat_1])).
% 1.00/1.20  thf(t130_relat_1, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i]:
% 1.00/1.20     ( ( v1_relat_1 @ C ) =>
% 1.00/1.20       ( ( r1_tarski @ A @ B ) =>
% 1.00/1.20         ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 1.00/1.20  thf('20', plain,
% 1.00/1.20      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.00/1.20         (~ (r1_tarski @ X11 @ X12)
% 1.00/1.20          | ~ (v1_relat_1 @ X13)
% 1.00/1.20          | ((k8_relat_1 @ X11 @ (k8_relat_1 @ X12 @ X13))
% 1.00/1.20              = (k8_relat_1 @ X11 @ X13)))),
% 1.00/1.20      inference('cnf', [status(esa)], [t130_relat_1])).
% 1.00/1.20  thf('21', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.20         (~ (v1_relat_1 @ X1)
% 1.00/1.20          | ((k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)) @ 
% 1.00/1.20              (k8_relat_1 @ X0 @ X2))
% 1.00/1.20              = (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)) @ X2))
% 1.00/1.20          | ~ (v1_relat_1 @ X2))),
% 1.00/1.20      inference('sup-', [status(thm)], ['19', '20'])).
% 1.00/1.20  thf('22', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (((k8_relat_1 @ X1 @ X0)
% 1.00/1.20            = (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0))
% 1.00/1.20          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 1.00/1.20          | ~ (v1_relat_1 @ X0)
% 1.00/1.20          | ~ (v1_relat_1 @ X0))),
% 1.00/1.20      inference('sup+', [status(thm)], ['18', '21'])).
% 1.00/1.20  thf('23', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (~ (v1_relat_1 @ X0)
% 1.00/1.20          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 1.00/1.20          | ((k8_relat_1 @ X1 @ X0)
% 1.00/1.20              = (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['22'])).
% 1.00/1.20  thf('24', plain,
% 1.00/1.20      (![X2 : $i, X3 : $i]:
% 1.00/1.20         ((v1_relat_1 @ (k8_relat_1 @ X2 @ X3)) | ~ (v1_relat_1 @ X3))),
% 1.00/1.20      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 1.00/1.20  thf('25', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (((k8_relat_1 @ X1 @ X0)
% 1.00/1.20            = (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0))
% 1.00/1.20          | ~ (v1_relat_1 @ X0))),
% 1.00/1.20      inference('clc', [status(thm)], ['23', '24'])).
% 1.00/1.20  thf('26', plain,
% 1.00/1.20      (![X2 : $i, X3 : $i]:
% 1.00/1.20         ((v1_relat_1 @ (k8_relat_1 @ X2 @ X3)) | ~ (v1_relat_1 @ X3))),
% 1.00/1.20      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 1.00/1.20  thf('27', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (((k8_relat_1 @ (k2_relat_1 @ X0) @ (k8_relat_1 @ X1 @ X0))
% 1.00/1.20            = (k8_relat_1 @ X1 @ X0))
% 1.00/1.20          | ~ (v1_relat_1 @ X0))),
% 1.00/1.20      inference('clc', [status(thm)], ['12', '13'])).
% 1.00/1.20  thf('28', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf(cc2_relset_1, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i]:
% 1.00/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.00/1.20       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.00/1.20  thf('29', plain,
% 1.00/1.20      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.00/1.20         ((v5_relat_1 @ X20 @ X22)
% 1.00/1.20          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.00/1.20      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.00/1.20  thf('30', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 1.00/1.20      inference('sup-', [status(thm)], ['28', '29'])).
% 1.00/1.20  thf(d19_relat_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( v1_relat_1 @ B ) =>
% 1.00/1.20       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.00/1.20  thf('31', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (~ (v5_relat_1 @ X0 @ X1)
% 1.00/1.20          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.00/1.20          | ~ (v1_relat_1 @ X0))),
% 1.00/1.20      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.00/1.20  thf('32', plain,
% 1.00/1.20      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 1.00/1.20      inference('sup-', [status(thm)], ['30', '31'])).
% 1.00/1.20  thf('33', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf(cc1_relset_1, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i]:
% 1.00/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.00/1.20       ( v1_relat_1 @ C ) ))).
% 1.00/1.20  thf('34', plain,
% 1.00/1.20      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.00/1.20         ((v1_relat_1 @ X17)
% 1.00/1.20          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.00/1.20      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.00/1.20  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 1.00/1.20      inference('sup-', [status(thm)], ['33', '34'])).
% 1.00/1.20  thf('36', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 1.00/1.20      inference('demod', [status(thm)], ['32', '35'])).
% 1.00/1.20  thf('37', plain,
% 1.00/1.20      (![X8 : $i, X9 : $i]:
% 1.00/1.20         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 1.00/1.20          | ((k8_relat_1 @ X9 @ X8) = (X8))
% 1.00/1.20          | ~ (v1_relat_1 @ X8))),
% 1.00/1.20      inference('cnf', [status(esa)], [t125_relat_1])).
% 1.00/1.20  thf('38', plain,
% 1.00/1.20      ((~ (v1_relat_1 @ sk_D) | ((k8_relat_1 @ sk_A @ sk_D) = (sk_D)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['36', '37'])).
% 1.00/1.20  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 1.00/1.20      inference('sup-', [status(thm)], ['33', '34'])).
% 1.00/1.20  thf('40', plain, (((k8_relat_1 @ sk_A @ sk_D) = (sk_D))),
% 1.00/1.20      inference('demod', [status(thm)], ['38', '39'])).
% 1.00/1.20  thf('41', plain,
% 1.00/1.20      (![X6 : $i, X7 : $i]:
% 1.00/1.20         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X6 @ X7)) @ 
% 1.00/1.20           (k2_relat_1 @ X7))
% 1.00/1.20          | ~ (v1_relat_1 @ X7))),
% 1.00/1.20      inference('cnf', [status(esa)], [t118_relat_1])).
% 1.00/1.20  thf('42', plain,
% 1.00/1.20      (((r1_tarski @ (k2_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))
% 1.00/1.20        | ~ (v1_relat_1 @ sk_D))),
% 1.00/1.20      inference('sup+', [status(thm)], ['40', '41'])).
% 1.00/1.20  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 1.00/1.20      inference('sup-', [status(thm)], ['33', '34'])).
% 1.00/1.20  thf('44', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))),
% 1.00/1.20      inference('demod', [status(thm)], ['42', '43'])).
% 1.00/1.20  thf('45', plain,
% 1.00/1.20      (![X8 : $i, X9 : $i]:
% 1.00/1.20         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 1.00/1.20          | ((k8_relat_1 @ X9 @ X8) = (X8))
% 1.00/1.20          | ~ (v1_relat_1 @ X8))),
% 1.00/1.20      inference('cnf', [status(esa)], [t125_relat_1])).
% 1.00/1.20  thf('46', plain,
% 1.00/1.20      ((~ (v1_relat_1 @ sk_D)
% 1.00/1.20        | ((k8_relat_1 @ (k2_relat_1 @ sk_D) @ sk_D) = (sk_D)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['44', '45'])).
% 1.00/1.20  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 1.00/1.20      inference('sup-', [status(thm)], ['33', '34'])).
% 1.00/1.20  thf('48', plain, (((k8_relat_1 @ (k2_relat_1 @ sk_D) @ sk_D) = (sk_D))),
% 1.00/1.20      inference('demod', [status(thm)], ['46', '47'])).
% 1.00/1.20  thf('49', plain,
% 1.00/1.20      (![X4 : $i, X5 : $i]:
% 1.00/1.20         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X4 @ X5)) @ X4)
% 1.00/1.20          | ~ (v1_relat_1 @ X5))),
% 1.00/1.20      inference('cnf', [status(esa)], [t116_relat_1])).
% 1.00/1.20  thf(t131_relat_1, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i]:
% 1.00/1.20     ( ( v1_relat_1 @ C ) =>
% 1.00/1.20       ( ( r1_tarski @ A @ B ) =>
% 1.00/1.20         ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ))).
% 1.00/1.20  thf('50', plain,
% 1.00/1.20      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.00/1.20         (~ (r1_tarski @ X14 @ X15)
% 1.00/1.20          | ~ (v1_relat_1 @ X16)
% 1.00/1.20          | (r1_tarski @ (k8_relat_1 @ X14 @ X16) @ (k8_relat_1 @ X15 @ X16)))),
% 1.00/1.20      inference('cnf', [status(esa)], [t131_relat_1])).
% 1.00/1.20  thf('51', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.20         (~ (v1_relat_1 @ X1)
% 1.00/1.20          | (r1_tarski @ 
% 1.00/1.20             (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)) @ X2) @ 
% 1.00/1.20             (k8_relat_1 @ X0 @ X2))
% 1.00/1.20          | ~ (v1_relat_1 @ X2))),
% 1.00/1.20      inference('sup-', [status(thm)], ['49', '50'])).
% 1.00/1.20  thf('52', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((r1_tarski @ 
% 1.00/1.20           (k8_relat_1 @ 
% 1.00/1.20            (k2_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_D) @ X0)) @ sk_D) @ 
% 1.00/1.20           sk_D)
% 1.00/1.20          | ~ (v1_relat_1 @ sk_D)
% 1.00/1.20          | ~ (v1_relat_1 @ X0))),
% 1.00/1.20      inference('sup+', [status(thm)], ['48', '51'])).
% 1.00/1.20  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 1.00/1.20      inference('sup-', [status(thm)], ['33', '34'])).
% 1.00/1.20  thf('54', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((r1_tarski @ 
% 1.00/1.20           (k8_relat_1 @ 
% 1.00/1.20            (k2_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_D) @ X0)) @ sk_D) @ 
% 1.00/1.20           sk_D)
% 1.00/1.20          | ~ (v1_relat_1 @ X0))),
% 1.00/1.20      inference('demod', [status(thm)], ['52', '53'])).
% 1.00/1.20  thf('55', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((r1_tarski @ 
% 1.00/1.20           (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_D) @ sk_D)
% 1.00/1.20          | ~ (v1_relat_1 @ sk_D)
% 1.00/1.20          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 1.00/1.20      inference('sup+', [status(thm)], ['27', '54'])).
% 1.00/1.20  thf('56', plain, ((v1_relat_1 @ sk_D)),
% 1.00/1.20      inference('sup-', [status(thm)], ['33', '34'])).
% 1.00/1.20  thf('57', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((r1_tarski @ 
% 1.00/1.20           (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_D) @ sk_D)
% 1.00/1.20          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 1.00/1.20      inference('demod', [status(thm)], ['55', '56'])).
% 1.00/1.20  thf('58', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (~ (v1_relat_1 @ sk_D)
% 1.00/1.20          | (r1_tarski @ 
% 1.00/1.20             (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_D) @ 
% 1.00/1.20             sk_D))),
% 1.00/1.20      inference('sup-', [status(thm)], ['26', '57'])).
% 1.00/1.20  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 1.00/1.20      inference('sup-', [status(thm)], ['33', '34'])).
% 1.00/1.20  thf('60', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (r1_tarski @ 
% 1.00/1.20          (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_D) @ sk_D)),
% 1.00/1.20      inference('demod', [status(thm)], ['58', '59'])).
% 1.00/1.20  thf('61', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_D) @ sk_D) | ~ (v1_relat_1 @ sk_D))),
% 1.00/1.20      inference('sup+', [status(thm)], ['25', '60'])).
% 1.00/1.20  thf('62', plain, ((v1_relat_1 @ sk_D)),
% 1.00/1.20      inference('sup-', [status(thm)], ['33', '34'])).
% 1.00/1.20  thf('63', plain, (![X0 : $i]: (r1_tarski @ (k8_relat_1 @ X0 @ sk_D) @ sk_D)),
% 1.00/1.20      inference('demod', [status(thm)], ['61', '62'])).
% 1.00/1.20  thf('64', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf(t4_relset_1, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.00/1.20     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 1.00/1.20       ( ( r1_tarski @ A @ D ) =>
% 1.00/1.20         ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 1.00/1.20  thf('65', plain,
% 1.00/1.20      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.00/1.20         ((m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.00/1.20          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.00/1.20          | ~ (r1_tarski @ X31 @ X34))),
% 1.00/1.20      inference('cnf', [status(esa)], [t4_relset_1])).
% 1.00/1.20  thf('66', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (~ (r1_tarski @ X0 @ sk_D)
% 1.00/1.20          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A))))),
% 1.00/1.20      inference('sup-', [status(thm)], ['64', '65'])).
% 1.00/1.20  thf('67', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 1.00/1.20          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['63', '66'])).
% 1.00/1.20  thf('68', plain,
% 1.00/1.20      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.00/1.20         ((v5_relat_1 @ X20 @ X22)
% 1.00/1.20          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.00/1.20      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.00/1.20  thf('69', plain,
% 1.00/1.20      (![X0 : $i]: (v5_relat_1 @ (k8_relat_1 @ X0 @ sk_D) @ sk_A)),
% 1.00/1.20      inference('sup-', [status(thm)], ['67', '68'])).
% 1.00/1.20  thf('70', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (~ (v5_relat_1 @ X0 @ X1)
% 1.00/1.20          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.00/1.20          | ~ (v1_relat_1 @ X0))),
% 1.00/1.20      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.00/1.20  thf('71', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))
% 1.00/1.20          | (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_A))),
% 1.00/1.20      inference('sup-', [status(thm)], ['69', '70'])).
% 1.00/1.20  thf('72', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 1.00/1.20          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['63', '66'])).
% 1.00/1.20  thf('73', plain,
% 1.00/1.20      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.00/1.20         ((v1_relat_1 @ X17)
% 1.00/1.20          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.00/1.20      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.00/1.20  thf('74', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))),
% 1.00/1.20      inference('sup-', [status(thm)], ['72', '73'])).
% 1.00/1.20  thf('75', plain,
% 1.00/1.20      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_A)),
% 1.00/1.20      inference('demod', [status(thm)], ['71', '74'])).
% 1.00/1.20  thf('76', plain,
% 1.00/1.20      (![X8 : $i, X9 : $i]:
% 1.00/1.20         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 1.00/1.20          | ((k8_relat_1 @ X9 @ X8) = (X8))
% 1.00/1.20          | ~ (v1_relat_1 @ X8))),
% 1.00/1.20      inference('cnf', [status(esa)], [t125_relat_1])).
% 1.00/1.20  thf('77', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))
% 1.00/1.20          | ((k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 1.00/1.20              = (k8_relat_1 @ X0 @ sk_D)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['75', '76'])).
% 1.00/1.20  thf('78', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))),
% 1.00/1.20      inference('sup-', [status(thm)], ['72', '73'])).
% 1.00/1.20  thf('79', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 1.00/1.20           = (k8_relat_1 @ X0 @ sk_D))),
% 1.00/1.20      inference('demod', [status(thm)], ['77', '78'])).
% 1.00/1.20  thf('80', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (((k8_relat_1 @ (k2_relat_1 @ X0) @ (k8_relat_1 @ X1 @ X0))
% 1.00/1.20            = (k8_relat_1 @ X1 @ X0))
% 1.00/1.20          | ~ (v1_relat_1 @ X0))),
% 1.00/1.20      inference('clc', [status(thm)], ['12', '13'])).
% 1.00/1.20  thf('81', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (((k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ 
% 1.00/1.20            (k8_relat_1 @ X0 @ sk_D))
% 1.00/1.20            = (k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D)))
% 1.00/1.20          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 1.00/1.20      inference('sup+', [status(thm)], ['79', '80'])).
% 1.00/1.20  thf('82', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 1.00/1.20           = (k8_relat_1 @ X0 @ sk_D))),
% 1.00/1.20      inference('demod', [status(thm)], ['77', '78'])).
% 1.00/1.20  thf('83', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))),
% 1.00/1.20      inference('sup-', [status(thm)], ['72', '73'])).
% 1.00/1.20  thf('84', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ 
% 1.00/1.20           (k8_relat_1 @ X0 @ sk_D)) = (k8_relat_1 @ X0 @ sk_D))),
% 1.00/1.20      inference('demod', [status(thm)], ['81', '82', '83'])).
% 1.00/1.20  thf('85', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (((k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ sk_D))
% 1.00/1.20            = (k8_relat_1 @ X0 @ sk_D))
% 1.00/1.20          | ~ (v1_relat_1 @ sk_D))),
% 1.00/1.20      inference('sup+', [status(thm)], ['17', '84'])).
% 1.00/1.20  thf('86', plain, ((v1_relat_1 @ sk_D)),
% 1.00/1.20      inference('sup-', [status(thm)], ['33', '34'])).
% 1.00/1.20  thf('87', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ sk_D))
% 1.00/1.20           = (k8_relat_1 @ X0 @ sk_D))),
% 1.00/1.20      inference('demod', [status(thm)], ['85', '86'])).
% 1.00/1.20  thf('88', plain,
% 1.00/1.20      (![X4 : $i, X5 : $i]:
% 1.00/1.20         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X4 @ X5)) @ X4)
% 1.00/1.20          | ~ (v1_relat_1 @ X5))),
% 1.00/1.20      inference('cnf', [status(esa)], [t116_relat_1])).
% 1.00/1.20  thf('89', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X0)
% 1.00/1.20          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 1.00/1.20      inference('sup+', [status(thm)], ['87', '88'])).
% 1.00/1.20  thf('90', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))),
% 1.00/1.20      inference('sup-', [status(thm)], ['72', '73'])).
% 1.00/1.20  thf('91', plain,
% 1.00/1.20      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X0)),
% 1.00/1.20      inference('demod', [status(thm)], ['89', '90'])).
% 1.00/1.20  thf('92', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 1.00/1.20          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['63', '66'])).
% 1.00/1.20  thf(t14_relset_1, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.00/1.20     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.00/1.20       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 1.00/1.20         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 1.00/1.20  thf('93', plain,
% 1.00/1.20      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.00/1.20         (~ (r1_tarski @ (k2_relat_1 @ X27) @ X28)
% 1.00/1.20          | (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 1.00/1.20          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.00/1.20      inference('cnf', [status(esa)], [t14_relset_1])).
% 1.00/1.20  thf('94', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 1.00/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 1.00/1.20          | ~ (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X1))),
% 1.00/1.20      inference('sup-', [status(thm)], ['92', '93'])).
% 1.00/1.20  thf('95', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 1.00/1.20          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['91', '94'])).
% 1.00/1.20  thf('96', plain, ($false), inference('demod', [status(thm)], ['4', '95'])).
% 1.00/1.20  
% 1.00/1.20  % SZS output end Refutation
% 1.00/1.20  
% 1.00/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
