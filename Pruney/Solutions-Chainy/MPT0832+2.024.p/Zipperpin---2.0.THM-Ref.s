%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RL2Yu8MNRJ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:31 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 473 expanded)
%              Number of leaves         :   30 ( 156 expanded)
%              Depth                    :   19
%              Number of atoms          :  826 (4006 expanded)
%              Number of equality atoms :   25 (  57 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( ( k6_relset_1 @ X29 @ X30 @ X27 @ X28 )
        = ( k8_relat_1 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k8_relat_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['10','15'])).

thf(t118_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X13 @ X14 ) ) @ ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t118_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( ( k8_relat_1 @ X16 @ X15 )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) )
      | ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) )
        = ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) )
        = ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['5','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X11 @ X12 ) ) @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X0 @ X1 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X0 @ X1 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('37',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['10','15'])).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( ( k8_relat_1 @ X16 @ X15 )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k8_relat_1 @ sk_A @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('41',plain,
    ( ( k8_relat_1 @ sk_A @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X11 @ X12 ) ) @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf(t131_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ) )).

thf('43',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( r1_tarski @ ( k8_relat_1 @ X21 @ X23 ) @ ( k8_relat_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t131_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ X2 ) @ ( k8_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) ) @ sk_D ) @ sk_D )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) ) @ sk_D ) @ sk_D )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_D ) @ sk_D )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['36','47'])).

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf('49',plain,(
    ! [X17: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X17 ) @ X17 )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X11 @ X12 ) ) @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf(t130_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('51',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( ( k8_relat_1 @ X18 @ ( k8_relat_1 @ X19 @ X20 ) )
        = ( k8_relat_1 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t130_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ ( k8_relat_1 @ X0 @ X2 ) )
        = ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
        = ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ X0 )
        = ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
        = ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) )
        = ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('60',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ sk_D )
      = ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ sk_D )
      = ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('63',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('66',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_D ) @ sk_D ) ),
    inference(demod,[status(thm)],['48','61','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ( ( r1_tarski @ A @ D )
       => ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('69',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r1_tarski @ X35 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_relset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('72',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X32 )
      | ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['4','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RL2Yu8MNRJ
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:41:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.31/1.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.31/1.50  % Solved by: fo/fo7.sh
% 1.31/1.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.31/1.50  % done 1432 iterations in 1.058s
% 1.31/1.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.31/1.50  % SZS output start Refutation
% 1.31/1.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.31/1.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.31/1.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.31/1.50  thf(sk_A_type, type, sk_A: $i).
% 1.31/1.50  thf(sk_D_type, type, sk_D: $i).
% 1.31/1.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.31/1.50  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 1.31/1.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.31/1.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.31/1.50  thf(sk_B_type, type, sk_B: $i).
% 1.31/1.50  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 1.31/1.50  thf(sk_C_type, type, sk_C: $i).
% 1.31/1.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.31/1.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.31/1.50  thf(t35_relset_1, conjecture,
% 1.31/1.50    (![A:$i,B:$i,C:$i,D:$i]:
% 1.31/1.50     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.31/1.50       ( m1_subset_1 @
% 1.31/1.50         ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 1.31/1.50         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 1.31/1.50  thf(zf_stmt_0, negated_conjecture,
% 1.31/1.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.31/1.50        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.31/1.50          ( m1_subset_1 @
% 1.31/1.50            ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 1.31/1.50            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )),
% 1.31/1.50    inference('cnf.neg', [status(esa)], [t35_relset_1])).
% 1.31/1.50  thf('0', plain,
% 1.31/1.50      (~ (m1_subset_1 @ (k6_relset_1 @ sk_C @ sk_A @ sk_B @ sk_D) @ 
% 1.31/1.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.31/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.50  thf('1', plain,
% 1.31/1.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.31/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.50  thf(redefinition_k6_relset_1, axiom,
% 1.31/1.50    (![A:$i,B:$i,C:$i,D:$i]:
% 1.31/1.50     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.31/1.50       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 1.31/1.50  thf('2', plain,
% 1.31/1.50      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.31/1.50         (((k6_relset_1 @ X29 @ X30 @ X27 @ X28) = (k8_relat_1 @ X27 @ X28))
% 1.31/1.50          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.31/1.50      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 1.31/1.50  thf('3', plain,
% 1.31/1.50      (![X0 : $i]:
% 1.31/1.50         ((k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 1.31/1.50      inference('sup-', [status(thm)], ['1', '2'])).
% 1.31/1.50  thf('4', plain,
% 1.31/1.50      (~ (m1_subset_1 @ (k8_relat_1 @ sk_B @ sk_D) @ 
% 1.31/1.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.31/1.50      inference('demod', [status(thm)], ['0', '3'])).
% 1.31/1.50  thf(dt_k8_relat_1, axiom,
% 1.31/1.50    (![A:$i,B:$i]:
% 1.31/1.50     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 1.31/1.50  thf('5', plain,
% 1.31/1.50      (![X7 : $i, X8 : $i]:
% 1.31/1.50         ((v1_relat_1 @ (k8_relat_1 @ X7 @ X8)) | ~ (v1_relat_1 @ X8))),
% 1.31/1.50      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 1.31/1.50  thf('6', plain,
% 1.31/1.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.31/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.51  thf(cc2_relset_1, axiom,
% 1.31/1.51    (![A:$i,B:$i,C:$i]:
% 1.31/1.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.31/1.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.31/1.51  thf('7', plain,
% 1.31/1.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.31/1.51         ((v5_relat_1 @ X24 @ X26)
% 1.31/1.51          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.31/1.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.31/1.51  thf('8', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 1.31/1.51      inference('sup-', [status(thm)], ['6', '7'])).
% 1.31/1.51  thf(d19_relat_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]:
% 1.31/1.51     ( ( v1_relat_1 @ B ) =>
% 1.31/1.51       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.31/1.51  thf('9', plain,
% 1.31/1.51      (![X5 : $i, X6 : $i]:
% 1.31/1.51         (~ (v5_relat_1 @ X5 @ X6)
% 1.31/1.51          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 1.31/1.51          | ~ (v1_relat_1 @ X5))),
% 1.31/1.51      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.31/1.51  thf('10', plain,
% 1.31/1.51      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 1.31/1.51      inference('sup-', [status(thm)], ['8', '9'])).
% 1.31/1.51  thf('11', plain,
% 1.31/1.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.31/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.51  thf(cc2_relat_1, axiom,
% 1.31/1.51    (![A:$i]:
% 1.31/1.51     ( ( v1_relat_1 @ A ) =>
% 1.31/1.51       ( ![B:$i]:
% 1.31/1.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.31/1.51  thf('12', plain,
% 1.31/1.51      (![X3 : $i, X4 : $i]:
% 1.31/1.51         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.31/1.51          | (v1_relat_1 @ X3)
% 1.31/1.51          | ~ (v1_relat_1 @ X4))),
% 1.31/1.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.31/1.51  thf('13', plain,
% 1.31/1.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.31/1.51      inference('sup-', [status(thm)], ['11', '12'])).
% 1.31/1.51  thf(fc6_relat_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.31/1.51  thf('14', plain,
% 1.31/1.51      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 1.31/1.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.31/1.51  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 1.31/1.51      inference('demod', [status(thm)], ['13', '14'])).
% 1.31/1.51  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 1.31/1.51      inference('demod', [status(thm)], ['10', '15'])).
% 1.31/1.51  thf(t118_relat_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]:
% 1.31/1.51     ( ( v1_relat_1 @ B ) =>
% 1.31/1.51       ( r1_tarski @
% 1.31/1.51         ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ))).
% 1.31/1.51  thf('17', plain,
% 1.31/1.51      (![X13 : $i, X14 : $i]:
% 1.31/1.51         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X13 @ X14)) @ 
% 1.31/1.51           (k2_relat_1 @ X14))
% 1.31/1.51          | ~ (v1_relat_1 @ X14))),
% 1.31/1.51      inference('cnf', [status(esa)], [t118_relat_1])).
% 1.31/1.51  thf(t1_xboole_1, axiom,
% 1.31/1.51    (![A:$i,B:$i,C:$i]:
% 1.31/1.51     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.31/1.51       ( r1_tarski @ A @ C ) ))).
% 1.31/1.51  thf('18', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.51         (~ (r1_tarski @ X0 @ X1)
% 1.31/1.51          | ~ (r1_tarski @ X1 @ X2)
% 1.31/1.51          | (r1_tarski @ X0 @ X2))),
% 1.31/1.51      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.31/1.51  thf('19', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.51         (~ (v1_relat_1 @ X0)
% 1.31/1.51          | (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X2)
% 1.31/1.51          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X2))),
% 1.31/1.51      inference('sup-', [status(thm)], ['17', '18'])).
% 1.31/1.51  thf('20', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_A)
% 1.31/1.51          | ~ (v1_relat_1 @ sk_D))),
% 1.31/1.51      inference('sup-', [status(thm)], ['16', '19'])).
% 1.31/1.51  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 1.31/1.51      inference('demod', [status(thm)], ['13', '14'])).
% 1.31/1.51  thf('22', plain,
% 1.31/1.51      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_A)),
% 1.31/1.51      inference('demod', [status(thm)], ['20', '21'])).
% 1.31/1.51  thf(t125_relat_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]:
% 1.31/1.51     ( ( v1_relat_1 @ B ) =>
% 1.31/1.51       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.31/1.51         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 1.31/1.51  thf('23', plain,
% 1.31/1.51      (![X15 : $i, X16 : $i]:
% 1.31/1.51         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 1.31/1.51          | ((k8_relat_1 @ X16 @ X15) = (X15))
% 1.31/1.51          | ~ (v1_relat_1 @ X15))),
% 1.31/1.51      inference('cnf', [status(esa)], [t125_relat_1])).
% 1.31/1.51  thf('24', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))
% 1.31/1.51          | ((k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 1.31/1.51              = (k8_relat_1 @ X0 @ sk_D)))),
% 1.31/1.51      inference('sup-', [status(thm)], ['22', '23'])).
% 1.31/1.51  thf('25', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         (~ (v1_relat_1 @ sk_D)
% 1.31/1.51          | ((k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 1.31/1.51              = (k8_relat_1 @ X0 @ sk_D)))),
% 1.31/1.51      inference('sup-', [status(thm)], ['5', '24'])).
% 1.31/1.51  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 1.31/1.51      inference('demod', [status(thm)], ['13', '14'])).
% 1.31/1.51  thf('27', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         ((k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 1.31/1.51           = (k8_relat_1 @ X0 @ sk_D))),
% 1.31/1.51      inference('demod', [status(thm)], ['25', '26'])).
% 1.31/1.51  thf(t116_relat_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]:
% 1.31/1.51     ( ( v1_relat_1 @ B ) =>
% 1.31/1.51       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 1.31/1.51  thf('28', plain,
% 1.31/1.51      (![X11 : $i, X12 : $i]:
% 1.31/1.51         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X11 @ X12)) @ X11)
% 1.31/1.51          | ~ (v1_relat_1 @ X12))),
% 1.31/1.51      inference('cnf', [status(esa)], [t116_relat_1])).
% 1.31/1.51  thf('29', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.51         (~ (v1_relat_1 @ X0)
% 1.31/1.51          | (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X2)
% 1.31/1.51          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X2))),
% 1.31/1.51      inference('sup-', [status(thm)], ['17', '18'])).
% 1.31/1.51  thf('30', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.51         (~ (v1_relat_1 @ X1)
% 1.31/1.51          | (r1_tarski @ 
% 1.31/1.51             (k2_relat_1 @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X0 @ X1))) @ X0)
% 1.31/1.51          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1)))),
% 1.31/1.51      inference('sup-', [status(thm)], ['28', '29'])).
% 1.31/1.51  thf('31', plain,
% 1.31/1.51      (![X7 : $i, X8 : $i]:
% 1.31/1.51         ((v1_relat_1 @ (k8_relat_1 @ X7 @ X8)) | ~ (v1_relat_1 @ X8))),
% 1.31/1.51      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 1.31/1.51  thf('32', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.51         ((r1_tarski @ 
% 1.31/1.51           (k2_relat_1 @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X0 @ X1))) @ X0)
% 1.31/1.51          | ~ (v1_relat_1 @ X1))),
% 1.31/1.51      inference('clc', [status(thm)], ['30', '31'])).
% 1.31/1.51  thf('33', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X0)
% 1.31/1.51          | ~ (v1_relat_1 @ sk_D))),
% 1.31/1.51      inference('sup+', [status(thm)], ['27', '32'])).
% 1.31/1.51  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 1.31/1.51      inference('demod', [status(thm)], ['13', '14'])).
% 1.31/1.51  thf('35', plain,
% 1.31/1.51      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X0)),
% 1.31/1.51      inference('demod', [status(thm)], ['33', '34'])).
% 1.31/1.51  thf('36', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         ((k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 1.31/1.51           = (k8_relat_1 @ X0 @ sk_D))),
% 1.31/1.51      inference('demod', [status(thm)], ['25', '26'])).
% 1.31/1.51  thf('37', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 1.31/1.51      inference('demod', [status(thm)], ['10', '15'])).
% 1.31/1.51  thf('38', plain,
% 1.31/1.51      (![X15 : $i, X16 : $i]:
% 1.31/1.51         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 1.31/1.51          | ((k8_relat_1 @ X16 @ X15) = (X15))
% 1.31/1.51          | ~ (v1_relat_1 @ X15))),
% 1.31/1.51      inference('cnf', [status(esa)], [t125_relat_1])).
% 1.31/1.51  thf('39', plain,
% 1.31/1.51      ((~ (v1_relat_1 @ sk_D) | ((k8_relat_1 @ sk_A @ sk_D) = (sk_D)))),
% 1.31/1.51      inference('sup-', [status(thm)], ['37', '38'])).
% 1.31/1.51  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 1.31/1.51      inference('demod', [status(thm)], ['13', '14'])).
% 1.31/1.51  thf('41', plain, (((k8_relat_1 @ sk_A @ sk_D) = (sk_D))),
% 1.31/1.51      inference('demod', [status(thm)], ['39', '40'])).
% 1.31/1.51  thf('42', plain,
% 1.31/1.51      (![X11 : $i, X12 : $i]:
% 1.31/1.51         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X11 @ X12)) @ X11)
% 1.31/1.51          | ~ (v1_relat_1 @ X12))),
% 1.31/1.51      inference('cnf', [status(esa)], [t116_relat_1])).
% 1.31/1.51  thf(t131_relat_1, axiom,
% 1.31/1.51    (![A:$i,B:$i,C:$i]:
% 1.31/1.51     ( ( v1_relat_1 @ C ) =>
% 1.31/1.51       ( ( r1_tarski @ A @ B ) =>
% 1.31/1.51         ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ))).
% 1.31/1.51  thf('43', plain,
% 1.31/1.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.31/1.51         (~ (r1_tarski @ X21 @ X22)
% 1.31/1.51          | ~ (v1_relat_1 @ X23)
% 1.31/1.51          | (r1_tarski @ (k8_relat_1 @ X21 @ X23) @ (k8_relat_1 @ X22 @ X23)))),
% 1.31/1.51      inference('cnf', [status(esa)], [t131_relat_1])).
% 1.31/1.51  thf('44', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.51         (~ (v1_relat_1 @ X1)
% 1.31/1.51          | (r1_tarski @ 
% 1.31/1.51             (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)) @ X2) @ 
% 1.31/1.51             (k8_relat_1 @ X0 @ X2))
% 1.31/1.51          | ~ (v1_relat_1 @ X2))),
% 1.31/1.51      inference('sup-', [status(thm)], ['42', '43'])).
% 1.31/1.51  thf('45', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         ((r1_tarski @ 
% 1.31/1.51           (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ X0)) @ sk_D) @ sk_D)
% 1.31/1.51          | ~ (v1_relat_1 @ sk_D)
% 1.31/1.51          | ~ (v1_relat_1 @ X0))),
% 1.31/1.51      inference('sup+', [status(thm)], ['41', '44'])).
% 1.31/1.51  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 1.31/1.51      inference('demod', [status(thm)], ['13', '14'])).
% 1.31/1.51  thf('47', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         ((r1_tarski @ 
% 1.31/1.51           (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ X0)) @ sk_D) @ sk_D)
% 1.31/1.51          | ~ (v1_relat_1 @ X0))),
% 1.31/1.51      inference('demod', [status(thm)], ['45', '46'])).
% 1.31/1.51  thf('48', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         ((r1_tarski @ 
% 1.31/1.51           (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_D) @ sk_D)
% 1.31/1.51          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['36', '47'])).
% 1.31/1.51  thf(t126_relat_1, axiom,
% 1.31/1.51    (![A:$i]:
% 1.31/1.51     ( ( v1_relat_1 @ A ) =>
% 1.31/1.51       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 1.31/1.51  thf('49', plain,
% 1.31/1.51      (![X17 : $i]:
% 1.31/1.51         (((k8_relat_1 @ (k2_relat_1 @ X17) @ X17) = (X17))
% 1.31/1.51          | ~ (v1_relat_1 @ X17))),
% 1.31/1.51      inference('cnf', [status(esa)], [t126_relat_1])).
% 1.31/1.51  thf('50', plain,
% 1.31/1.51      (![X11 : $i, X12 : $i]:
% 1.31/1.51         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X11 @ X12)) @ X11)
% 1.31/1.51          | ~ (v1_relat_1 @ X12))),
% 1.31/1.51      inference('cnf', [status(esa)], [t116_relat_1])).
% 1.31/1.51  thf(t130_relat_1, axiom,
% 1.31/1.51    (![A:$i,B:$i,C:$i]:
% 1.31/1.51     ( ( v1_relat_1 @ C ) =>
% 1.31/1.51       ( ( r1_tarski @ A @ B ) =>
% 1.31/1.51         ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 1.31/1.51  thf('51', plain,
% 1.31/1.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.31/1.51         (~ (r1_tarski @ X18 @ X19)
% 1.31/1.51          | ~ (v1_relat_1 @ X20)
% 1.31/1.51          | ((k8_relat_1 @ X18 @ (k8_relat_1 @ X19 @ X20))
% 1.31/1.51              = (k8_relat_1 @ X18 @ X20)))),
% 1.31/1.51      inference('cnf', [status(esa)], [t130_relat_1])).
% 1.31/1.51  thf('52', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.51         (~ (v1_relat_1 @ X1)
% 1.31/1.51          | ((k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)) @ 
% 1.31/1.51              (k8_relat_1 @ X0 @ X2))
% 1.31/1.51              = (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)) @ X2))
% 1.31/1.51          | ~ (v1_relat_1 @ X2))),
% 1.31/1.51      inference('sup-', [status(thm)], ['50', '51'])).
% 1.31/1.51  thf('53', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (((k8_relat_1 @ X1 @ X0)
% 1.31/1.51            = (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0))
% 1.31/1.51          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 1.31/1.51          | ~ (v1_relat_1 @ X0)
% 1.31/1.51          | ~ (v1_relat_1 @ X0))),
% 1.31/1.51      inference('sup+', [status(thm)], ['49', '52'])).
% 1.31/1.51  thf('54', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (~ (v1_relat_1 @ X0)
% 1.31/1.51          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 1.31/1.51          | ((k8_relat_1 @ X1 @ X0)
% 1.31/1.51              = (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0)))),
% 1.31/1.51      inference('simplify', [status(thm)], ['53'])).
% 1.31/1.51  thf('55', plain,
% 1.31/1.51      (![X7 : $i, X8 : $i]:
% 1.31/1.51         ((v1_relat_1 @ (k8_relat_1 @ X7 @ X8)) | ~ (v1_relat_1 @ X8))),
% 1.31/1.51      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 1.31/1.51  thf('56', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (((k8_relat_1 @ X1 @ X0)
% 1.31/1.51            = (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0))
% 1.31/1.51          | ~ (v1_relat_1 @ X0))),
% 1.31/1.51      inference('clc', [status(thm)], ['54', '55'])).
% 1.31/1.51  thf('57', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         ((k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 1.31/1.51           = (k8_relat_1 @ X0 @ sk_D))),
% 1.31/1.51      inference('demod', [status(thm)], ['25', '26'])).
% 1.31/1.51  thf('58', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         (((k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 1.31/1.51            = (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_D))
% 1.31/1.51          | ~ (v1_relat_1 @ sk_D))),
% 1.31/1.51      inference('sup+', [status(thm)], ['56', '57'])).
% 1.31/1.51  thf('59', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         ((k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 1.31/1.51           = (k8_relat_1 @ X0 @ sk_D))),
% 1.31/1.51      inference('demod', [status(thm)], ['25', '26'])).
% 1.31/1.51  thf('60', plain, ((v1_relat_1 @ sk_D)),
% 1.31/1.51      inference('demod', [status(thm)], ['13', '14'])).
% 1.31/1.51  thf('61', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         ((k8_relat_1 @ X0 @ sk_D)
% 1.31/1.51           = (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_D))),
% 1.31/1.51      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.31/1.51  thf('62', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         ((k8_relat_1 @ X0 @ sk_D)
% 1.31/1.51           = (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_D))),
% 1.31/1.51      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.31/1.51  thf('63', plain,
% 1.31/1.51      (![X7 : $i, X8 : $i]:
% 1.31/1.51         ((v1_relat_1 @ (k8_relat_1 @ X7 @ X8)) | ~ (v1_relat_1 @ X8))),
% 1.31/1.51      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 1.31/1.51  thf('64', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         ((v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) | ~ (v1_relat_1 @ sk_D))),
% 1.31/1.51      inference('sup+', [status(thm)], ['62', '63'])).
% 1.31/1.51  thf('65', plain, ((v1_relat_1 @ sk_D)),
% 1.31/1.51      inference('demod', [status(thm)], ['13', '14'])).
% 1.31/1.51  thf('66', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))),
% 1.31/1.51      inference('demod', [status(thm)], ['64', '65'])).
% 1.31/1.51  thf('67', plain, (![X0 : $i]: (r1_tarski @ (k8_relat_1 @ X0 @ sk_D) @ sk_D)),
% 1.31/1.51      inference('demod', [status(thm)], ['48', '61', '66'])).
% 1.31/1.51  thf('68', plain,
% 1.31/1.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.31/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.51  thf(t4_relset_1, axiom,
% 1.31/1.51    (![A:$i,B:$i,C:$i,D:$i]:
% 1.31/1.51     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 1.31/1.51       ( ( r1_tarski @ A @ D ) =>
% 1.31/1.51         ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 1.31/1.51  thf('69', plain,
% 1.31/1.51      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.31/1.51         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.31/1.51          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.31/1.51          | ~ (r1_tarski @ X35 @ X38))),
% 1.31/1.51      inference('cnf', [status(esa)], [t4_relset_1])).
% 1.31/1.51  thf('70', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         (~ (r1_tarski @ X0 @ sk_D)
% 1.31/1.51          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A))))),
% 1.31/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.31/1.51  thf('71', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 1.31/1.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.31/1.51      inference('sup-', [status(thm)], ['67', '70'])).
% 1.31/1.51  thf(t14_relset_1, axiom,
% 1.31/1.51    (![A:$i,B:$i,C:$i,D:$i]:
% 1.31/1.51     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.31/1.51       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 1.31/1.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 1.31/1.51  thf('72', plain,
% 1.31/1.51      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.31/1.51         (~ (r1_tarski @ (k2_relat_1 @ X31) @ X32)
% 1.31/1.51          | (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 1.31/1.51          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 1.31/1.51      inference('cnf', [status(esa)], [t14_relset_1])).
% 1.31/1.51  thf('73', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 1.31/1.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 1.31/1.51          | ~ (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X1))),
% 1.31/1.51      inference('sup-', [status(thm)], ['71', '72'])).
% 1.31/1.51  thf('74', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 1.31/1.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0)))),
% 1.31/1.51      inference('sup-', [status(thm)], ['35', '73'])).
% 1.31/1.51  thf('75', plain, ($false), inference('demod', [status(thm)], ['4', '74'])).
% 1.31/1.51  
% 1.31/1.51  % SZS output end Refutation
% 1.31/1.51  
% 1.31/1.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
