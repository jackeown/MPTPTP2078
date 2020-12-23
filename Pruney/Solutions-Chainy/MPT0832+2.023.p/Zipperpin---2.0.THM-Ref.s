%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EYxK4YH68A

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:31 EST 2020

% Result     : Theorem 12.46s
% Output     : Refutation 12.46s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 283 expanded)
%              Number of leaves         :   35 (  96 expanded)
%              Depth                    :   21
%              Number of atoms          : 1000 (2622 expanded)
%              Number of equality atoms :   18 (  38 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( ( k6_relset_1 @ X38 @ X39 @ X36 @ X37 )
        = ( k8_relat_1 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X16 @ X17 ) ) @ ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( ( k8_relat_1 @ X19 @ X18 )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X14 @ X15 ) ) @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf('36',plain,(
    ! [X20: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X20 ) @ X20 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X16 @ X17 ) ) @ ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t118_relat_1])).

thf(t131_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ) )).

thf('38',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X26 )
      | ( r1_tarski @ ( k8_relat_1 @ X24 @ X26 ) @ ( k8_relat_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t131_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X2 ) @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X14 @ X15 ) ) @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf(t130_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('43',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( ( k8_relat_1 @ X21 @ ( k8_relat_1 @ X22 @ X23 ) )
        = ( k8_relat_1 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t130_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ ( k8_relat_1 @ X0 @ X2 ) )
        = ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X20: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X20 ) @ X20 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('46',plain,(
    ! [X20: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X20 ) @ X20 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('47',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X14 @ X15 ) ) @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X26 )
      | ( r1_tarski @ ( k8_relat_1 @ X24 @ X26 ) @ ( k8_relat_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t131_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ( ( r1_tarski @ A @ D )
       => ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('63',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( r1_tarski @ X43 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t4_relset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('67',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('68',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X30 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relset_1 @ sk_C @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) ) @ ( k1_zfmisc_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('71',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ sk_C @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) )
      = ( k1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ ( k1_zfmisc_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','72'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('74',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('76',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X40 ) @ X41 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X40 ) @ X42 )
      | ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) )
      | ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('79',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
      | ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','83'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['4','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EYxK4YH68A
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:02:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 12.46/12.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.46/12.63  % Solved by: fo/fo7.sh
% 12.46/12.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.46/12.63  % done 10305 iterations in 12.193s
% 12.46/12.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.46/12.63  % SZS output start Refutation
% 12.46/12.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 12.46/12.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 12.46/12.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.46/12.63  thf(sk_D_type, type, sk_D: $i).
% 12.46/12.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.46/12.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 12.46/12.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 12.46/12.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 12.46/12.63  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 12.46/12.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.46/12.63  thf(sk_A_type, type, sk_A: $i).
% 12.46/12.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 12.46/12.63  thf(sk_B_type, type, sk_B: $i).
% 12.46/12.63  thf(sk_C_type, type, sk_C: $i).
% 12.46/12.63  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 12.46/12.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 12.46/12.63  thf(t35_relset_1, conjecture,
% 12.46/12.63    (![A:$i,B:$i,C:$i,D:$i]:
% 12.46/12.63     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 12.46/12.63       ( m1_subset_1 @
% 12.46/12.63         ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 12.46/12.63         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 12.46/12.63  thf(zf_stmt_0, negated_conjecture,
% 12.46/12.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 12.46/12.63        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 12.46/12.63          ( m1_subset_1 @
% 12.46/12.63            ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 12.46/12.63            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )),
% 12.46/12.63    inference('cnf.neg', [status(esa)], [t35_relset_1])).
% 12.46/12.63  thf('0', plain,
% 12.46/12.63      (~ (m1_subset_1 @ (k6_relset_1 @ sk_C @ sk_A @ sk_B @ sk_D) @ 
% 12.46/12.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 12.46/12.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.46/12.63  thf('1', plain,
% 12.46/12.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 12.46/12.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.46/12.63  thf(redefinition_k6_relset_1, axiom,
% 12.46/12.63    (![A:$i,B:$i,C:$i,D:$i]:
% 12.46/12.63     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.46/12.63       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 12.46/12.63  thf('2', plain,
% 12.46/12.63      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 12.46/12.63         (((k6_relset_1 @ X38 @ X39 @ X36 @ X37) = (k8_relat_1 @ X36 @ X37))
% 12.46/12.63          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 12.46/12.63      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 12.46/12.63  thf('3', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         ((k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 12.46/12.63      inference('sup-', [status(thm)], ['1', '2'])).
% 12.46/12.63  thf('4', plain,
% 12.46/12.63      (~ (m1_subset_1 @ (k8_relat_1 @ sk_B @ sk_D) @ 
% 12.46/12.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 12.46/12.63      inference('demod', [status(thm)], ['0', '3'])).
% 12.46/12.63  thf(dt_k8_relat_1, axiom,
% 12.46/12.63    (![A:$i,B:$i]:
% 12.46/12.63     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 12.46/12.63  thf('5', plain,
% 12.46/12.63      (![X10 : $i, X11 : $i]:
% 12.46/12.63         ((v1_relat_1 @ (k8_relat_1 @ X10 @ X11)) | ~ (v1_relat_1 @ X11))),
% 12.46/12.63      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 12.46/12.63  thf('6', plain,
% 12.46/12.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 12.46/12.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.46/12.63  thf(cc2_relset_1, axiom,
% 12.46/12.63    (![A:$i,B:$i,C:$i]:
% 12.46/12.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.46/12.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 12.46/12.63  thf('7', plain,
% 12.46/12.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 12.46/12.63         ((v5_relat_1 @ X27 @ X29)
% 12.46/12.63          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 12.46/12.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 12.46/12.63  thf('8', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 12.46/12.63      inference('sup-', [status(thm)], ['6', '7'])).
% 12.46/12.63  thf(d19_relat_1, axiom,
% 12.46/12.63    (![A:$i,B:$i]:
% 12.46/12.63     ( ( v1_relat_1 @ B ) =>
% 12.46/12.63       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 12.46/12.63  thf('9', plain,
% 12.46/12.63      (![X8 : $i, X9 : $i]:
% 12.46/12.63         (~ (v5_relat_1 @ X8 @ X9)
% 12.46/12.63          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 12.46/12.63          | ~ (v1_relat_1 @ X8))),
% 12.46/12.63      inference('cnf', [status(esa)], [d19_relat_1])).
% 12.46/12.63  thf('10', plain,
% 12.46/12.63      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 12.46/12.63      inference('sup-', [status(thm)], ['8', '9'])).
% 12.46/12.63  thf('11', plain,
% 12.46/12.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 12.46/12.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.46/12.63  thf(cc2_relat_1, axiom,
% 12.46/12.63    (![A:$i]:
% 12.46/12.63     ( ( v1_relat_1 @ A ) =>
% 12.46/12.63       ( ![B:$i]:
% 12.46/12.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 12.46/12.63  thf('12', plain,
% 12.46/12.63      (![X6 : $i, X7 : $i]:
% 12.46/12.63         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 12.46/12.63          | (v1_relat_1 @ X6)
% 12.46/12.63          | ~ (v1_relat_1 @ X7))),
% 12.46/12.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 12.46/12.63  thf('13', plain,
% 12.46/12.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_D))),
% 12.46/12.63      inference('sup-', [status(thm)], ['11', '12'])).
% 12.46/12.63  thf(fc6_relat_1, axiom,
% 12.46/12.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 12.46/12.63  thf('14', plain,
% 12.46/12.63      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 12.46/12.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 12.46/12.63  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 12.46/12.63      inference('demod', [status(thm)], ['13', '14'])).
% 12.46/12.63  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 12.46/12.63      inference('demod', [status(thm)], ['10', '15'])).
% 12.46/12.63  thf(t118_relat_1, axiom,
% 12.46/12.63    (![A:$i,B:$i]:
% 12.46/12.63     ( ( v1_relat_1 @ B ) =>
% 12.46/12.63       ( r1_tarski @
% 12.46/12.63         ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ))).
% 12.46/12.63  thf('17', plain,
% 12.46/12.63      (![X16 : $i, X17 : $i]:
% 12.46/12.63         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X16 @ X17)) @ 
% 12.46/12.63           (k2_relat_1 @ X17))
% 12.46/12.63          | ~ (v1_relat_1 @ X17))),
% 12.46/12.63      inference('cnf', [status(esa)], [t118_relat_1])).
% 12.46/12.63  thf(t1_xboole_1, axiom,
% 12.46/12.63    (![A:$i,B:$i,C:$i]:
% 12.46/12.63     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 12.46/12.63       ( r1_tarski @ A @ C ) ))).
% 12.46/12.63  thf('18', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.46/12.63         (~ (r1_tarski @ X0 @ X1)
% 12.46/12.63          | ~ (r1_tarski @ X1 @ X2)
% 12.46/12.63          | (r1_tarski @ X0 @ X2))),
% 12.46/12.63      inference('cnf', [status(esa)], [t1_xboole_1])).
% 12.46/12.63  thf('19', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ X0)
% 12.46/12.63          | (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X2)
% 12.46/12.63          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X2))),
% 12.46/12.63      inference('sup-', [status(thm)], ['17', '18'])).
% 12.46/12.63  thf('20', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_A)
% 12.46/12.63          | ~ (v1_relat_1 @ sk_D))),
% 12.46/12.63      inference('sup-', [status(thm)], ['16', '19'])).
% 12.46/12.63  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 12.46/12.63      inference('demod', [status(thm)], ['13', '14'])).
% 12.46/12.63  thf('22', plain,
% 12.46/12.63      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_A)),
% 12.46/12.63      inference('demod', [status(thm)], ['20', '21'])).
% 12.46/12.63  thf(t125_relat_1, axiom,
% 12.46/12.63    (![A:$i,B:$i]:
% 12.46/12.63     ( ( v1_relat_1 @ B ) =>
% 12.46/12.63       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 12.46/12.63         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 12.46/12.63  thf('23', plain,
% 12.46/12.63      (![X18 : $i, X19 : $i]:
% 12.46/12.63         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 12.46/12.63          | ((k8_relat_1 @ X19 @ X18) = (X18))
% 12.46/12.63          | ~ (v1_relat_1 @ X18))),
% 12.46/12.63      inference('cnf', [status(esa)], [t125_relat_1])).
% 12.46/12.63  thf('24', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))
% 12.46/12.63          | ((k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 12.46/12.63              = (k8_relat_1 @ X0 @ sk_D)))),
% 12.46/12.63      inference('sup-', [status(thm)], ['22', '23'])).
% 12.46/12.63  thf('25', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ sk_D)
% 12.46/12.63          | ((k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 12.46/12.63              = (k8_relat_1 @ X0 @ sk_D)))),
% 12.46/12.63      inference('sup-', [status(thm)], ['5', '24'])).
% 12.46/12.63  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 12.46/12.63      inference('demod', [status(thm)], ['13', '14'])).
% 12.46/12.63  thf('27', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         ((k8_relat_1 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 12.46/12.63           = (k8_relat_1 @ X0 @ sk_D))),
% 12.46/12.63      inference('demod', [status(thm)], ['25', '26'])).
% 12.46/12.63  thf(t116_relat_1, axiom,
% 12.46/12.63    (![A:$i,B:$i]:
% 12.46/12.63     ( ( v1_relat_1 @ B ) =>
% 12.46/12.63       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 12.46/12.63  thf('28', plain,
% 12.46/12.63      (![X14 : $i, X15 : $i]:
% 12.46/12.63         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X14 @ X15)) @ X14)
% 12.46/12.63          | ~ (v1_relat_1 @ X15))),
% 12.46/12.63      inference('cnf', [status(esa)], [t116_relat_1])).
% 12.46/12.63  thf('29', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ X0)
% 12.46/12.63          | (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X2)
% 12.46/12.63          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X2))),
% 12.46/12.63      inference('sup-', [status(thm)], ['17', '18'])).
% 12.46/12.63  thf('30', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ X1)
% 12.46/12.63          | (r1_tarski @ 
% 12.46/12.63             (k2_relat_1 @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X0 @ X1))) @ X0)
% 12.46/12.63          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1)))),
% 12.46/12.63      inference('sup-', [status(thm)], ['28', '29'])).
% 12.46/12.63  thf('31', plain,
% 12.46/12.63      (![X10 : $i, X11 : $i]:
% 12.46/12.63         ((v1_relat_1 @ (k8_relat_1 @ X10 @ X11)) | ~ (v1_relat_1 @ X11))),
% 12.46/12.63      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 12.46/12.63  thf('32', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.46/12.63         ((r1_tarski @ 
% 12.46/12.63           (k2_relat_1 @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X0 @ X1))) @ X0)
% 12.46/12.63          | ~ (v1_relat_1 @ X1))),
% 12.46/12.63      inference('clc', [status(thm)], ['30', '31'])).
% 12.46/12.63  thf('33', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X0)
% 12.46/12.63          | ~ (v1_relat_1 @ sk_D))),
% 12.46/12.63      inference('sup+', [status(thm)], ['27', '32'])).
% 12.46/12.63  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 12.46/12.63      inference('demod', [status(thm)], ['13', '14'])).
% 12.46/12.63  thf('35', plain,
% 12.46/12.63      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X0)),
% 12.46/12.63      inference('demod', [status(thm)], ['33', '34'])).
% 12.46/12.63  thf(t126_relat_1, axiom,
% 12.46/12.63    (![A:$i]:
% 12.46/12.63     ( ( v1_relat_1 @ A ) =>
% 12.46/12.63       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 12.46/12.63  thf('36', plain,
% 12.46/12.63      (![X20 : $i]:
% 12.46/12.63         (((k8_relat_1 @ (k2_relat_1 @ X20) @ X20) = (X20))
% 12.46/12.63          | ~ (v1_relat_1 @ X20))),
% 12.46/12.63      inference('cnf', [status(esa)], [t126_relat_1])).
% 12.46/12.63  thf('37', plain,
% 12.46/12.63      (![X16 : $i, X17 : $i]:
% 12.46/12.63         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X16 @ X17)) @ 
% 12.46/12.63           (k2_relat_1 @ X17))
% 12.46/12.63          | ~ (v1_relat_1 @ X17))),
% 12.46/12.63      inference('cnf', [status(esa)], [t118_relat_1])).
% 12.46/12.63  thf(t131_relat_1, axiom,
% 12.46/12.63    (![A:$i,B:$i,C:$i]:
% 12.46/12.63     ( ( v1_relat_1 @ C ) =>
% 12.46/12.63       ( ( r1_tarski @ A @ B ) =>
% 12.46/12.63         ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ))).
% 12.46/12.63  thf('38', plain,
% 12.46/12.63      (![X24 : $i, X25 : $i, X26 : $i]:
% 12.46/12.63         (~ (r1_tarski @ X24 @ X25)
% 12.46/12.63          | ~ (v1_relat_1 @ X26)
% 12.46/12.63          | (r1_tarski @ (k8_relat_1 @ X24 @ X26) @ (k8_relat_1 @ X25 @ X26)))),
% 12.46/12.63      inference('cnf', [status(esa)], [t131_relat_1])).
% 12.46/12.63  thf('39', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ X0)
% 12.46/12.63          | (r1_tarski @ 
% 12.46/12.63             (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X2) @ 
% 12.46/12.63             (k8_relat_1 @ (k2_relat_1 @ X0) @ X2))
% 12.46/12.63          | ~ (v1_relat_1 @ X2))),
% 12.46/12.63      inference('sup-', [status(thm)], ['37', '38'])).
% 12.46/12.63  thf('40', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i]:
% 12.46/12.63         ((r1_tarski @ 
% 12.46/12.63           (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0) @ X0)
% 12.46/12.63          | ~ (v1_relat_1 @ X0)
% 12.46/12.63          | ~ (v1_relat_1 @ X0)
% 12.46/12.63          | ~ (v1_relat_1 @ X0))),
% 12.46/12.63      inference('sup+', [status(thm)], ['36', '39'])).
% 12.46/12.63  thf('41', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ X0)
% 12.46/12.63          | (r1_tarski @ 
% 12.46/12.63             (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0) @ X0))),
% 12.46/12.63      inference('simplify', [status(thm)], ['40'])).
% 12.46/12.63  thf('42', plain,
% 12.46/12.63      (![X14 : $i, X15 : $i]:
% 12.46/12.63         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X14 @ X15)) @ X14)
% 12.46/12.63          | ~ (v1_relat_1 @ X15))),
% 12.46/12.63      inference('cnf', [status(esa)], [t116_relat_1])).
% 12.46/12.63  thf(t130_relat_1, axiom,
% 12.46/12.63    (![A:$i,B:$i,C:$i]:
% 12.46/12.63     ( ( v1_relat_1 @ C ) =>
% 12.46/12.63       ( ( r1_tarski @ A @ B ) =>
% 12.46/12.63         ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 12.46/12.63  thf('43', plain,
% 12.46/12.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 12.46/12.63         (~ (r1_tarski @ X21 @ X22)
% 12.46/12.63          | ~ (v1_relat_1 @ X23)
% 12.46/12.63          | ((k8_relat_1 @ X21 @ (k8_relat_1 @ X22 @ X23))
% 12.46/12.63              = (k8_relat_1 @ X21 @ X23)))),
% 12.46/12.63      inference('cnf', [status(esa)], [t130_relat_1])).
% 12.46/12.63  thf('44', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ X1)
% 12.46/12.63          | ((k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)) @ 
% 12.46/12.63              (k8_relat_1 @ X0 @ X2))
% 12.46/12.63              = (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)) @ X2))
% 12.46/12.63          | ~ (v1_relat_1 @ X2))),
% 12.46/12.63      inference('sup-', [status(thm)], ['42', '43'])).
% 12.46/12.63  thf('45', plain,
% 12.46/12.63      (![X20 : $i]:
% 12.46/12.63         (((k8_relat_1 @ (k2_relat_1 @ X20) @ X20) = (X20))
% 12.46/12.63          | ~ (v1_relat_1 @ X20))),
% 12.46/12.63      inference('cnf', [status(esa)], [t126_relat_1])).
% 12.46/12.63  thf('46', plain,
% 12.46/12.63      (![X20 : $i]:
% 12.46/12.63         (((k8_relat_1 @ (k2_relat_1 @ X20) @ X20) = (X20))
% 12.46/12.63          | ~ (v1_relat_1 @ X20))),
% 12.46/12.63      inference('cnf', [status(esa)], [t126_relat_1])).
% 12.46/12.63  thf('47', plain,
% 12.46/12.63      (![X14 : $i, X15 : $i]:
% 12.46/12.63         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X14 @ X15)) @ X14)
% 12.46/12.63          | ~ (v1_relat_1 @ X15))),
% 12.46/12.63      inference('cnf', [status(esa)], [t116_relat_1])).
% 12.46/12.63  thf('48', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         ((r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 12.46/12.63          | ~ (v1_relat_1 @ X0)
% 12.46/12.63          | ~ (v1_relat_1 @ X0))),
% 12.46/12.63      inference('sup+', [status(thm)], ['46', '47'])).
% 12.46/12.63  thf('49', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ X0)
% 12.46/12.63          | (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 12.46/12.63      inference('simplify', [status(thm)], ['48'])).
% 12.46/12.63  thf('50', plain,
% 12.46/12.63      (![X24 : $i, X25 : $i, X26 : $i]:
% 12.46/12.63         (~ (r1_tarski @ X24 @ X25)
% 12.46/12.63          | ~ (v1_relat_1 @ X26)
% 12.46/12.63          | (r1_tarski @ (k8_relat_1 @ X24 @ X26) @ (k8_relat_1 @ X25 @ X26)))),
% 12.46/12.63      inference('cnf', [status(esa)], [t131_relat_1])).
% 12.46/12.63  thf('51', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ X0)
% 12.46/12.63          | (r1_tarski @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X1) @ 
% 12.46/12.63             (k8_relat_1 @ (k2_relat_1 @ X0) @ X1))
% 12.46/12.63          | ~ (v1_relat_1 @ X1))),
% 12.46/12.63      inference('sup-', [status(thm)], ['49', '50'])).
% 12.46/12.63  thf('52', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         ((r1_tarski @ X0 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))
% 12.46/12.63          | ~ (v1_relat_1 @ X0)
% 12.46/12.63          | ~ (v1_relat_1 @ X0)
% 12.46/12.63          | ~ (v1_relat_1 @ X0))),
% 12.46/12.63      inference('sup+', [status(thm)], ['45', '51'])).
% 12.46/12.63  thf('53', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ X0)
% 12.46/12.63          | (r1_tarski @ X0 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)))),
% 12.46/12.63      inference('simplify', [status(thm)], ['52'])).
% 12.46/12.63  thf('54', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.46/12.63         (~ (r1_tarski @ X0 @ X1)
% 12.46/12.63          | ~ (r1_tarski @ X1 @ X2)
% 12.46/12.63          | (r1_tarski @ X0 @ X2))),
% 12.46/12.63      inference('cnf', [status(esa)], [t1_xboole_1])).
% 12.46/12.63  thf('55', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ X0)
% 12.46/12.63          | (r1_tarski @ X0 @ X1)
% 12.46/12.63          | ~ (r1_tarski @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0) @ X1))),
% 12.46/12.63      inference('sup-', [status(thm)], ['53', '54'])).
% 12.46/12.63  thf('56', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.46/12.63         (~ (r1_tarski @ 
% 12.46/12.63             (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0) @ X2)
% 12.46/12.63          | ~ (v1_relat_1 @ X0)
% 12.46/12.63          | ~ (v1_relat_1 @ X0)
% 12.46/12.63          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 12.46/12.63          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 12.46/12.63      inference('sup-', [status(thm)], ['44', '55'])).
% 12.46/12.63  thf('57', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 12.46/12.63          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 12.46/12.63          | ~ (v1_relat_1 @ X0)
% 12.46/12.63          | ~ (r1_tarski @ 
% 12.46/12.63               (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0) @ X2))),
% 12.46/12.63      inference('simplify', [status(thm)], ['56'])).
% 12.46/12.63  thf('58', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ X0)
% 12.46/12.63          | ~ (v1_relat_1 @ X0)
% 12.46/12.63          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0)
% 12.46/12.63          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 12.46/12.63      inference('sup-', [status(thm)], ['41', '57'])).
% 12.46/12.63  thf('59', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 12.46/12.63          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0)
% 12.46/12.63          | ~ (v1_relat_1 @ X0))),
% 12.46/12.63      inference('simplify', [status(thm)], ['58'])).
% 12.46/12.63  thf('60', plain,
% 12.46/12.63      (![X10 : $i, X11 : $i]:
% 12.46/12.63         ((v1_relat_1 @ (k8_relat_1 @ X10 @ X11)) | ~ (v1_relat_1 @ X11))),
% 12.46/12.63      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 12.46/12.63  thf('61', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ X0) | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0))),
% 12.46/12.63      inference('clc', [status(thm)], ['59', '60'])).
% 12.46/12.63  thf('62', plain,
% 12.46/12.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 12.46/12.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.46/12.63  thf(t4_relset_1, axiom,
% 12.46/12.63    (![A:$i,B:$i,C:$i,D:$i]:
% 12.46/12.63     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 12.46/12.63       ( ( r1_tarski @ A @ D ) =>
% 12.46/12.63         ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 12.46/12.63  thf('63', plain,
% 12.46/12.63      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 12.46/12.63         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 12.46/12.63          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 12.46/12.63          | ~ (r1_tarski @ X43 @ X46))),
% 12.46/12.63      inference('cnf', [status(esa)], [t4_relset_1])).
% 12.46/12.63  thf('64', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         (~ (r1_tarski @ X0 @ sk_D)
% 12.46/12.63          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A))))),
% 12.46/12.63      inference('sup-', [status(thm)], ['62', '63'])).
% 12.46/12.63  thf('65', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ sk_D)
% 12.46/12.63          | (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 12.46/12.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A))))),
% 12.46/12.63      inference('sup-', [status(thm)], ['61', '64'])).
% 12.46/12.63  thf('66', plain, ((v1_relat_1 @ sk_D)),
% 12.46/12.63      inference('demod', [status(thm)], ['13', '14'])).
% 12.46/12.63  thf('67', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 12.46/12.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 12.46/12.63      inference('demod', [status(thm)], ['65', '66'])).
% 12.46/12.63  thf(dt_k1_relset_1, axiom,
% 12.46/12.63    (![A:$i,B:$i,C:$i]:
% 12.46/12.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.46/12.63       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 12.46/12.63  thf('68', plain,
% 12.46/12.63      (![X30 : $i, X31 : $i, X32 : $i]:
% 12.46/12.63         ((m1_subset_1 @ (k1_relset_1 @ X30 @ X31 @ X32) @ (k1_zfmisc_1 @ X30))
% 12.46/12.63          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 12.46/12.63      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 12.46/12.63  thf('69', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         (m1_subset_1 @ 
% 12.46/12.63          (k1_relset_1 @ sk_C @ sk_A @ (k8_relat_1 @ X0 @ sk_D)) @ 
% 12.46/12.63          (k1_zfmisc_1 @ sk_C))),
% 12.46/12.63      inference('sup-', [status(thm)], ['67', '68'])).
% 12.46/12.63  thf('70', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 12.46/12.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 12.46/12.63      inference('demod', [status(thm)], ['65', '66'])).
% 12.46/12.63  thf(redefinition_k1_relset_1, axiom,
% 12.46/12.63    (![A:$i,B:$i,C:$i]:
% 12.46/12.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.46/12.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 12.46/12.63  thf('71', plain,
% 12.46/12.63      (![X33 : $i, X34 : $i, X35 : $i]:
% 12.46/12.63         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 12.46/12.63          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 12.46/12.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 12.46/12.63  thf('72', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         ((k1_relset_1 @ sk_C @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 12.46/12.63           = (k1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 12.46/12.63      inference('sup-', [status(thm)], ['70', '71'])).
% 12.46/12.63  thf('73', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         (m1_subset_1 @ (k1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ 
% 12.46/12.63          (k1_zfmisc_1 @ sk_C))),
% 12.46/12.63      inference('demod', [status(thm)], ['69', '72'])).
% 12.46/12.63  thf(t3_subset, axiom,
% 12.46/12.63    (![A:$i,B:$i]:
% 12.46/12.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 12.46/12.63  thf('74', plain,
% 12.46/12.63      (![X3 : $i, X4 : $i]:
% 12.46/12.63         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 12.46/12.63      inference('cnf', [status(esa)], [t3_subset])).
% 12.46/12.63  thf('75', plain,
% 12.46/12.63      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_C)),
% 12.46/12.63      inference('sup-', [status(thm)], ['73', '74'])).
% 12.46/12.63  thf(t11_relset_1, axiom,
% 12.46/12.63    (![A:$i,B:$i,C:$i]:
% 12.46/12.63     ( ( v1_relat_1 @ C ) =>
% 12.46/12.63       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 12.46/12.63           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 12.46/12.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 12.46/12.63  thf('76', plain,
% 12.46/12.63      (![X40 : $i, X41 : $i, X42 : $i]:
% 12.46/12.63         (~ (r1_tarski @ (k1_relat_1 @ X40) @ X41)
% 12.46/12.63          | ~ (r1_tarski @ (k2_relat_1 @ X40) @ X42)
% 12.46/12.63          | (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 12.46/12.63          | ~ (v1_relat_1 @ X40))),
% 12.46/12.63      inference('cnf', [status(esa)], [t11_relset_1])).
% 12.46/12.63  thf('77', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))
% 12.46/12.63          | (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 12.46/12.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 12.46/12.63          | ~ (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X1))),
% 12.46/12.63      inference('sup-', [status(thm)], ['75', '76'])).
% 12.46/12.63  thf('78', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 12.46/12.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 12.46/12.63      inference('demod', [status(thm)], ['65', '66'])).
% 12.46/12.63  thf('79', plain,
% 12.46/12.63      (![X6 : $i, X7 : $i]:
% 12.46/12.63         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 12.46/12.63          | (v1_relat_1 @ X6)
% 12.46/12.63          | ~ (v1_relat_1 @ X7))),
% 12.46/12.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 12.46/12.63  thf('80', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A))
% 12.46/12.63          | (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 12.46/12.63      inference('sup-', [status(thm)], ['78', '79'])).
% 12.46/12.63  thf('81', plain,
% 12.46/12.63      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 12.46/12.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 12.46/12.63  thf('82', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))),
% 12.46/12.63      inference('demod', [status(thm)], ['80', '81'])).
% 12.46/12.63  thf('83', plain,
% 12.46/12.63      (![X0 : $i, X1 : $i]:
% 12.46/12.63         ((m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 12.46/12.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 12.46/12.63          | ~ (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X1))),
% 12.46/12.63      inference('demod', [status(thm)], ['77', '82'])).
% 12.46/12.63  thf('84', plain,
% 12.46/12.63      (![X0 : $i]:
% 12.46/12.63         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 12.46/12.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0)))),
% 12.46/12.63      inference('sup-', [status(thm)], ['35', '83'])).
% 12.46/12.63  thf('85', plain, ($false), inference('demod', [status(thm)], ['4', '84'])).
% 12.46/12.63  
% 12.46/12.63  % SZS output end Refutation
% 12.46/12.63  
% 12.47/12.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
