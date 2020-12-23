%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bx9YEeU8Bm

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 143 expanded)
%              Number of leaves         :   31 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  834 (1880 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k8_relat_1 @ X3 @ X2 )
        = ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('1',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t23_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C )
        & ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C )
          & ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_funct_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19 )
        = ( k5_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ sk_A @ sk_B @ X0 @ X0 @ sk_C @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
    | ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('16',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['18','21'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X4 ) @ X5 )
      | ( ( k8_relat_1 @ X5 @ X4 )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k8_relat_1 @ sk_B @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('26',plain,
    ( ( k8_relat_1 @ sk_B @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('28',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['13','26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 )
      | ( X22 != X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('31',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( $false
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['28','32'])).

thf('34',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['29','31'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k7_relat_1 @ X9 @ X8 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X8 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19 )
        = ( k5_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ ( k6_relat_1 @ X0 ) @ sk_C )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('42',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('43',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('48',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6
        = ( k7_relat_1 @ X6 @ X7 ) )
      | ~ ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('52',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('54',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['45','52','53'])).

thf('55',plain,(
    r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ),
    inference('sup-',[status(thm)],['34','54'])).

thf('56',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C )
    | ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('57',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['33','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bx9YEeU8Bm
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:20:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 55 iterations in 0.016s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.46  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.20/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.46  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.46  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(t123_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) =>
% 0.20/0.46       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i]:
% 0.20/0.46         (((k8_relat_1 @ X3 @ X2) = (k5_relat_1 @ X2 @ (k6_relat_1 @ X3)))
% 0.20/0.46          | ~ (v1_relat_1 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.20/0.46  thf(dt_k6_partfun1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( m1_subset_1 @
% 0.20/0.46         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.20/0.46       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X27 : $i]:
% 0.20/0.46         (m1_subset_1 @ (k6_partfun1 @ X27) @ 
% 0.20/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.20/0.46  thf(redefinition_k6_partfun1, axiom,
% 0.20/0.46    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.46  thf('2', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X27 : $i]:
% 0.20/0.46         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 0.20/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.20/0.46      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf(t23_funct_2, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( ( r2_relset_1 @
% 0.20/0.46           A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ 
% 0.20/0.46           C ) & 
% 0.20/0.46         ( r2_relset_1 @
% 0.20/0.46           A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ 
% 0.20/0.46           C ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.46        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46          ( ( r2_relset_1 @
% 0.20/0.46              A @ B @ 
% 0.20/0.46              ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C ) & 
% 0.20/0.46            ( r2_relset_1 @
% 0.20/0.46              A @ B @ 
% 0.20/0.46              ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t23_funct_2])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(redefinition_k4_relset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.46     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.46         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.20/0.46       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.20/0.46          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.20/0.46          | ((k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19)
% 0.20/0.46              = (k5_relat_1 @ X16 @ X19)))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.20/0.46            = (k5_relat_1 @ sk_C @ X0))
% 0.20/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((k4_relset_1 @ sk_A @ sk_B @ X0 @ X0 @ sk_C @ (k6_relat_1 @ X0))
% 0.20/0.46           = (k5_relat_1 @ sk_C @ (k6_relat_1 @ X0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ 
% 0.20/0.46            sk_C) @ 
% 0.20/0.46           sk_C)
% 0.20/0.46        | ~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46             (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.46              (k6_partfun1 @ sk_B)) @ 
% 0.20/0.46             sk_C))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.46            (k6_partfun1 @ sk_B)) @ 
% 0.20/0.46           sk_C))
% 0.20/0.46         <= (~
% 0.20/0.46             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.46                (k6_partfun1 @ sk_B)) @ 
% 0.20/0.46               sk_C)))),
% 0.20/0.46      inference('split', [status(esa)], ['8'])).
% 0.20/0.46  thf('10', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.46            (k6_relat_1 @ sk_B)) @ 
% 0.20/0.46           sk_C))
% 0.20/0.46         <= (~
% 0.20/0.46             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.46                (k6_partfun1 @ sk_B)) @ 
% 0.20/0.46               sk_C)))),
% 0.20/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46           (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_C))
% 0.20/0.46         <= (~
% 0.20/0.46             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.46                (k6_partfun1 @ sk_B)) @ 
% 0.20/0.46               sk_C)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '11'])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (((~ (r2_relset_1 @ sk_A @ sk_B @ (k8_relat_1 @ sk_B @ sk_C) @ sk_C)
% 0.20/0.46         | ~ (v1_relat_1 @ sk_C)))
% 0.20/0.46         <= (~
% 0.20/0.46             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.46                (k6_partfun1 @ sk_B)) @ 
% 0.20/0.46               sk_C)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '12'])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(cc2_relset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.46         ((v5_relat_1 @ X13 @ X15)
% 0.20/0.46          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.46  thf('16', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.20/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.46  thf(d19_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) =>
% 0.20/0.46       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (v5_relat_1 @ X0 @ X1)
% 0.20/0.46          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.20/0.46          | ~ (v1_relat_1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(cc1_relset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( v1_relat_1 @ C ) ))).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.46         ((v1_relat_1 @ X10)
% 0.20/0.46          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.20/0.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.46  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.46  thf('22', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.20/0.46      inference('demod', [status(thm)], ['18', '21'])).
% 0.20/0.46  thf(t125_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) =>
% 0.20/0.46       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.46         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i]:
% 0.20/0.46         (~ (r1_tarski @ (k2_relat_1 @ X4) @ X5)
% 0.20/0.46          | ((k8_relat_1 @ X5 @ X4) = (X4))
% 0.20/0.46          | ~ (v1_relat_1 @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      ((~ (v1_relat_1 @ sk_C) | ((k8_relat_1 @ sk_B @ sk_C) = (sk_C)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.46  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.46  thf('26', plain, (((k8_relat_1 @ sk_B @ sk_C) = (sk_C))),
% 0.20/0.46      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.46  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      ((~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C))
% 0.20/0.46         <= (~
% 0.20/0.46             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.46                (k6_partfun1 @ sk_B)) @ 
% 0.20/0.46               sk_C)))),
% 0.20/0.46      inference('demod', [status(thm)], ['13', '26', '27'])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(redefinition_r2_relset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.46       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.20/0.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.20/0.46          | (r2_relset_1 @ X23 @ X24 @ X22 @ X25)
% 0.20/0.46          | ((X22) != (X25)))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.20/0.46  thf('31', plain,
% 0.20/0.46      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.46         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 0.20/0.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.46      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.46  thf('32', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.20/0.46      inference('sup-', [status(thm)], ['29', '31'])).
% 0.20/0.46  thf('33', plain,
% 0.20/0.46      (($false)
% 0.20/0.46         <= (~
% 0.20/0.46             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.46                (k6_partfun1 @ sk_B)) @ 
% 0.20/0.46               sk_C)))),
% 0.20/0.46      inference('demod', [status(thm)], ['28', '32'])).
% 0.20/0.46  thf('34', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.20/0.46      inference('sup-', [status(thm)], ['29', '31'])).
% 0.20/0.46  thf(t94_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) =>
% 0.20/0.46       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.20/0.46  thf('35', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]:
% 0.20/0.46         (((k7_relat_1 @ X9 @ X8) = (k5_relat_1 @ (k6_relat_1 @ X8) @ X9))
% 0.20/0.46          | ~ (v1_relat_1 @ X9))),
% 0.20/0.46      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.46  thf('36', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('37', plain,
% 0.20/0.46      (![X27 : $i]:
% 0.20/0.46         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 0.20/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.20/0.46      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf('38', plain,
% 0.20/0.46      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.20/0.46          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.20/0.46          | ((k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19)
% 0.20/0.46              = (k5_relat_1 @ X16 @ X19)))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.20/0.46  thf('39', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         (((k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 0.20/0.46            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.46  thf('40', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ (k6_relat_1 @ X0) @ sk_C)
% 0.20/0.46           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['36', '39'])).
% 0.20/0.46  thf('41', plain,
% 0.20/0.46      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ 
% 0.20/0.46            sk_C) @ 
% 0.20/0.46           sk_C))
% 0.20/0.46         <= (~
% 0.20/0.46             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.20/0.46                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.20/0.46               sk_C)))),
% 0.20/0.46      inference('split', [status(esa)], ['8'])).
% 0.20/0.46  thf('42', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.46  thf('43', plain,
% 0.20/0.46      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_relat_1 @ sk_A) @ 
% 0.20/0.46            sk_C) @ 
% 0.20/0.46           sk_C))
% 0.20/0.46         <= (~
% 0.20/0.46             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.20/0.46                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.20/0.46               sk_C)))),
% 0.20/0.46      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.46  thf('44', plain,
% 0.20/0.46      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46           (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) @ sk_C))
% 0.20/0.46         <= (~
% 0.20/0.46             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.20/0.46                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.20/0.46               sk_C)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['40', '43'])).
% 0.20/0.46  thf('45', plain,
% 0.20/0.46      (((~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_C @ sk_A) @ sk_C)
% 0.20/0.46         | ~ (v1_relat_1 @ sk_C)))
% 0.20/0.46         <= (~
% 0.20/0.46             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.20/0.46                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.20/0.46               sk_C)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['35', '44'])).
% 0.20/0.46  thf('46', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('47', plain,
% 0.20/0.46      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.46         ((v4_relat_1 @ X13 @ X14)
% 0.20/0.46          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.46  thf('48', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.20/0.46      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.46  thf(t209_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.46       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.46  thf('49', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i]:
% 0.20/0.46         (((X6) = (k7_relat_1 @ X6 @ X7))
% 0.20/0.46          | ~ (v4_relat_1 @ X6 @ X7)
% 0.20/0.46          | ~ (v1_relat_1 @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.46  thf('50', plain,
% 0.20/0.46      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.46  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.46  thf('52', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.46  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.46  thf('54', plain,
% 0.20/0.46      ((~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C))
% 0.20/0.46         <= (~
% 0.20/0.46             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.20/0.46                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.20/0.46               sk_C)))),
% 0.20/0.46      inference('demod', [status(thm)], ['45', '52', '53'])).
% 0.20/0.46  thf('55', plain,
% 0.20/0.46      (((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.20/0.46         sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['34', '54'])).
% 0.20/0.46  thf('56', plain,
% 0.20/0.46      (~
% 0.20/0.46       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 0.20/0.46         sk_C)) | 
% 0.20/0.46       ~
% 0.20/0.46       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.20/0.46         sk_C))),
% 0.20/0.46      inference('split', [status(esa)], ['8'])).
% 0.20/0.46  thf('57', plain,
% 0.20/0.46      (~
% 0.20/0.46       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.46         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 0.20/0.46         sk_C))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['55', '56'])).
% 0.20/0.46  thf('58', plain, ($false),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['33', '57'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
