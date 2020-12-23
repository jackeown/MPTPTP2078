%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QV2Mjd7V2x

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:50 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 154 expanded)
%              Number of leaves         :   35 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  836 (1884 expanded)
%              Number of equality atoms :   26 (  31 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

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

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
    | ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(split,[status(esa)],['1'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k8_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('6',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('7',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ sk_A @ sk_B @ X0 @ X0 @ sk_C @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(split,[status(esa)],['1'])).

thf('14',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X18 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('20',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['20','23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ( ( k8_relat_1 @ X10 @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k8_relat_1 @ sk_B @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k8_relat_1 @ sk_B @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['28','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('36',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_relset_1 @ X30 @ X31 @ X32 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['36'])).

thf('38',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf('40',plain,(
    r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ),
    inference(demod,[status(thm)],['17','34','38','39'])).

thf('41',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
    | ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(split,[status(esa)],['1'])).

thf('42',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['4','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('46',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ ( k6_relat_1 @ X0 ) @ sk_C )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf('57',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['35','37'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['50','57','58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QV2Mjd7V2x
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:21:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.18/0.33  % Number of cores: 8
% 0.18/0.33  % Python version: Python 3.6.8
% 0.18/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 95 iterations in 0.053s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.19/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.49  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.19/0.49  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.49  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.19/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.49  thf(t94_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) =>
% 0.19/0.49       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      (![X13 : $i, X14 : $i]:
% 0.19/0.49         (((k7_relat_1 @ X14 @ X13) = (k5_relat_1 @ (k6_relat_1 @ X13) @ X14))
% 0.19/0.49          | ~ (v1_relat_1 @ X14))),
% 0.19/0.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.49  thf(t23_funct_2, conjecture,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( ( r2_relset_1 @
% 0.19/0.49           A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ 
% 0.19/0.49           C ) & 
% 0.19/0.49         ( r2_relset_1 @
% 0.19/0.49           A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ 
% 0.19/0.49           C ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.49        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49          ( ( r2_relset_1 @
% 0.19/0.49              A @ B @ 
% 0.19/0.49              ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C ) & 
% 0.19/0.49            ( r2_relset_1 @
% 0.19/0.49              A @ B @ 
% 0.19/0.49              ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t23_funct_2])).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.49           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ 
% 0.19/0.49            sk_C) @ 
% 0.19/0.49           sk_C)
% 0.19/0.49        | ~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.49             (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.19/0.49              (k6_partfun1 @ sk_B)) @ 
% 0.19/0.49             sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.49           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ 
% 0.19/0.49            sk_C) @ 
% 0.19/0.49           sk_C))
% 0.19/0.49         <= (~
% 0.19/0.49             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.49               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.19/0.49                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.19/0.49               sk_C)))),
% 0.19/0.49      inference('split', [status(esa)], ['1'])).
% 0.19/0.49  thf(redefinition_k6_partfun1, axiom,
% 0.19/0.49    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.19/0.49  thf('3', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.49           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_relat_1 @ sk_A) @ 
% 0.19/0.49            sk_C) @ 
% 0.19/0.49           sk_C))
% 0.19/0.49         <= (~
% 0.19/0.49             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.49               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.19/0.49                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.19/0.49               sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.49  thf(t123_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) =>
% 0.19/0.49       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X7 : $i, X8 : $i]:
% 0.19/0.50         (((k8_relat_1 @ X8 @ X7) = (k5_relat_1 @ X7 @ (k6_relat_1 @ X8)))
% 0.19/0.50          | ~ (v1_relat_1 @ X7))),
% 0.19/0.50      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.19/0.50  thf(dt_k6_partfun1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( m1_subset_1 @
% 0.19/0.50         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.19/0.50       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X35 : $i]:
% 0.19/0.50         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 0.19/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.19/0.50  thf('7', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X35 : $i]:
% 0.19/0.50         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 0.19/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.19/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(redefinition_k4_relset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.50     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.50         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.19/0.50       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.19/0.50          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.19/0.50          | ((k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 0.19/0.50              = (k5_relat_1 @ X24 @ X27)))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.19/0.50            = (k5_relat_1 @ sk_C @ X0))
% 0.19/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((k4_relset_1 @ sk_A @ sk_B @ X0 @ X0 @ sk_C @ (k6_relat_1 @ X0))
% 0.19/0.50           = (k5_relat_1 @ sk_C @ (k6_relat_1 @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['8', '11'])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.50           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.19/0.50            (k6_partfun1 @ sk_B)) @ 
% 0.19/0.50           sk_C))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.50               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.19/0.50                (k6_partfun1 @ sk_B)) @ 
% 0.19/0.50               sk_C)))),
% 0.19/0.50      inference('split', [status(esa)], ['1'])).
% 0.19/0.50  thf('14', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.50           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.19/0.50            (k6_relat_1 @ sk_B)) @ 
% 0.19/0.50           sk_C))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.50               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.19/0.50                (k6_partfun1 @ sk_B)) @ 
% 0.19/0.50               sk_C)))),
% 0.19/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.50           (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_C))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.50               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.19/0.50                (k6_partfun1 @ sk_B)) @ 
% 0.19/0.50               sk_C)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['12', '15'])).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (((~ (r2_relset_1 @ sk_A @ sk_B @ (k8_relat_1 @ sk_B @ sk_C) @ sk_C)
% 0.19/0.50         | ~ (v1_relat_1 @ sk_C)))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.50               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.19/0.50                (k6_partfun1 @ sk_B)) @ 
% 0.19/0.50               sk_C)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['5', '16'])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(dt_k2_relset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.50         ((m1_subset_1 @ (k2_relset_1 @ X18 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))
% 0.19/0.50          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.50         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.19/0.50          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.19/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)], ['20', '23'])).
% 0.19/0.50  thf(t3_subset, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.50  thf('26', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.19/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.50  thf(t125_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ B ) =>
% 0.19/0.50       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.19/0.50         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i]:
% 0.19/0.50         (~ (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.19/0.50          | ((k8_relat_1 @ X10 @ X9) = (X9))
% 0.19/0.50          | ~ (v1_relat_1 @ X9))),
% 0.19/0.50      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      ((~ (v1_relat_1 @ sk_C) | ((k8_relat_1 @ sk_B @ sk_C) = (sk_C)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(cc2_relat_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.50  thf('30', plain,
% 0.19/0.50      (![X3 : $i, X4 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.19/0.50          | (v1_relat_1 @ X3)
% 0.19/0.50          | ~ (v1_relat_1 @ X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.19/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf(fc6_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.50  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.50  thf('34', plain, (((k8_relat_1 @ sk_B @ sk_C) = (sk_C))),
% 0.19/0.50      inference('demod', [status(thm)], ['28', '33'])).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(reflexivity_r2_relset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.50       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.19/0.50         ((r2_relset_1 @ X30 @ X31 @ X32 @ X32)
% 0.19/0.50          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.19/0.50          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.19/0.50      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.19/0.50  thf('37', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.19/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.19/0.50      inference('condensation', [status(thm)], ['36'])).
% 0.19/0.50  thf('38', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.19/0.50      inference('sup-', [status(thm)], ['35', '37'])).
% 0.19/0.50  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.50  thf('40', plain,
% 0.19/0.50      (((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.50         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 0.19/0.50         sk_C))),
% 0.19/0.50      inference('demod', [status(thm)], ['17', '34', '38', '39'])).
% 0.19/0.50  thf('41', plain,
% 0.19/0.50      (~
% 0.19/0.50       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.50         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.19/0.50         sk_C)) | 
% 0.19/0.50       ~
% 0.19/0.50       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.50         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 0.19/0.50         sk_C))),
% 0.19/0.50      inference('split', [status(esa)], ['1'])).
% 0.19/0.50  thf('42', plain,
% 0.19/0.50      (~
% 0.19/0.50       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.50         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.19/0.50         sk_C))),
% 0.19/0.50      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 0.19/0.50  thf('43', plain,
% 0.19/0.50      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.50          (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_relat_1 @ sk_A) @ sk_C) @ 
% 0.19/0.50          sk_C)),
% 0.19/0.50      inference('simpl_trail', [status(thm)], ['4', '42'])).
% 0.19/0.50  thf('44', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('45', plain,
% 0.19/0.50      (![X35 : $i]:
% 0.19/0.50         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 0.19/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.19/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf('46', plain,
% 0.19/0.50      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.19/0.50          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.19/0.50          | ((k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 0.19/0.50              = (k5_relat_1 @ X24 @ X27)))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.19/0.50  thf('47', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.50         (((k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 0.19/0.50            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.19/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.50  thf('48', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ (k6_relat_1 @ X0) @ sk_C)
% 0.19/0.50           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_C))),
% 0.19/0.50      inference('sup-', [status(thm)], ['44', '47'])).
% 0.19/0.50  thf('49', plain,
% 0.19/0.50      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.50          (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) @ sk_C)),
% 0.19/0.50      inference('demod', [status(thm)], ['43', '48'])).
% 0.19/0.50  thf('50', plain,
% 0.19/0.50      ((~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_C @ sk_A) @ sk_C)
% 0.19/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.50      inference('sup-', [status(thm)], ['0', '49'])).
% 0.19/0.50  thf('51', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(cc2_relset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.50  thf('52', plain,
% 0.19/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.50         ((v4_relat_1 @ X15 @ X16)
% 0.19/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.19/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.50  thf('53', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.19/0.50      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.50  thf(t209_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.19/0.50       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.19/0.50  thf('54', plain,
% 0.19/0.50      (![X11 : $i, X12 : $i]:
% 0.19/0.50         (((X11) = (k7_relat_1 @ X11 @ X12))
% 0.19/0.50          | ~ (v4_relat_1 @ X11 @ X12)
% 0.19/0.50          | ~ (v1_relat_1 @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.19/0.50  thf('55', plain,
% 0.19/0.50      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.19/0.50  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.50  thf('57', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['55', '56'])).
% 0.19/0.50  thf('58', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.19/0.50      inference('sup-', [status(thm)], ['35', '37'])).
% 0.19/0.50  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.50  thf('60', plain, ($false),
% 0.19/0.50      inference('demod', [status(thm)], ['50', '57', '58', '59'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
