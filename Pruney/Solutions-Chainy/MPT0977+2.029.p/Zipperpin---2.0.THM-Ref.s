%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Oi3ITKgf0C

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:48 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 170 expanded)
%              Number of leaves         :   34 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :  818 (2016 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

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

thf('0',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
    | ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k8_relat_1 @ X7 @ X6 )
        = ( k5_relat_1 @ X6 @ ( k6_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('5',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('6',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k4_relset_1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22 )
        = ( k5_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ sk_A @ sk_B @ X0 @ X0 @ sk_C @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('14',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('19',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['21','26'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ( ( k8_relat_1 @ X9 @ X8 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k8_relat_1 @ sk_B @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('31',plain,
    ( ( k8_relat_1 @ sk_B @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('33',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 )
      | ( X25 != X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('34',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_relset_1 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('37',plain,(
    r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ),
    inference(demod,[status(thm)],['16','31','35','36'])).

thf('38',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
    | ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['3','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k4_relset_1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22 )
        = ( k5_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ ( k6_relat_1 @ X0 ) @ sk_C )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('52',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('54',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('56',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['54','55'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('57',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('60',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['32','34'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['40','45','60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Oi3ITKgf0C
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 55 iterations in 0.030s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.35/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.35/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.35/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.54  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.35/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.35/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.35/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.35/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.54  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.35/0.54  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.35/0.54  thf(t23_funct_2, conjecture,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( r2_relset_1 @
% 0.35/0.54           A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ 
% 0.35/0.54           C ) & 
% 0.35/0.54         ( r2_relset_1 @
% 0.35/0.54           A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ 
% 0.35/0.54           C ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.54        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54          ( ( r2_relset_1 @
% 0.35/0.54              A @ B @ 
% 0.35/0.54              ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C ) & 
% 0.35/0.54            ( r2_relset_1 @
% 0.35/0.54              A @ B @ 
% 0.35/0.54              ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t23_funct_2])).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ 
% 0.35/0.54            sk_C) @ 
% 0.35/0.54           sk_C)
% 0.35/0.54        | ~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54             (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.35/0.54              (k6_partfun1 @ sk_B)) @ 
% 0.35/0.54             sk_C))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ 
% 0.35/0.54            sk_C) @ 
% 0.35/0.54           sk_C))
% 0.35/0.54         <= (~
% 0.35/0.54             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.35/0.54                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.35/0.54               sk_C)))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf(redefinition_k6_partfun1, axiom,
% 0.35/0.54    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.35/0.54  thf('2', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_relat_1 @ sk_A) @ 
% 0.35/0.54            sk_C) @ 
% 0.35/0.54           sk_C))
% 0.35/0.54         <= (~
% 0.35/0.54             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.35/0.54                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.35/0.54               sk_C)))),
% 0.35/0.54      inference('demod', [status(thm)], ['1', '2'])).
% 0.35/0.54  thf(t123_relat_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ B ) =>
% 0.35/0.54       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      (![X6 : $i, X7 : $i]:
% 0.35/0.54         (((k8_relat_1 @ X7 @ X6) = (k5_relat_1 @ X6 @ (k6_relat_1 @ X7)))
% 0.35/0.54          | ~ (v1_relat_1 @ X6))),
% 0.35/0.54      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.35/0.54  thf(dt_k6_partfun1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( m1_subset_1 @
% 0.35/0.54         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.35/0.54       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      (![X30 : $i]:
% 0.35/0.54         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 0.35/0.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.35/0.54  thf('6', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      (![X30 : $i]:
% 0.35/0.54         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 0.35/0.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.35/0.54      inference('demod', [status(thm)], ['5', '6'])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(redefinition_k4_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.35/0.54     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.35/0.54         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.35/0.54       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.35/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.35/0.54          | ((k4_relset_1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22)
% 0.35/0.54              = (k5_relat_1 @ X19 @ X22)))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.35/0.54  thf('10', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.54         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.35/0.54            = (k5_relat_1 @ sk_C @ X0))
% 0.35/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.35/0.54  thf('11', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((k4_relset_1 @ sk_A @ sk_B @ X0 @ X0 @ sk_C @ (k6_relat_1 @ X0))
% 0.35/0.54           = (k5_relat_1 @ sk_C @ (k6_relat_1 @ X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['7', '10'])).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.35/0.54            (k6_partfun1 @ sk_B)) @ 
% 0.35/0.54           sk_C))
% 0.35/0.54         <= (~
% 0.35/0.54             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.35/0.54                (k6_partfun1 @ sk_B)) @ 
% 0.35/0.54               sk_C)))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('13', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.35/0.54            (k6_relat_1 @ sk_B)) @ 
% 0.35/0.54           sk_C))
% 0.35/0.54         <= (~
% 0.35/0.54             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.35/0.54                (k6_partfun1 @ sk_B)) @ 
% 0.35/0.54               sk_C)))),
% 0.35/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54           (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_C))
% 0.35/0.54         <= (~
% 0.35/0.54             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.35/0.54                (k6_partfun1 @ sk_B)) @ 
% 0.35/0.54               sk_C)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['11', '14'])).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      (((~ (r2_relset_1 @ sk_A @ sk_B @ (k8_relat_1 @ sk_B @ sk_C) @ sk_C)
% 0.35/0.54         | ~ (v1_relat_1 @ sk_C)))
% 0.35/0.54         <= (~
% 0.35/0.54             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.35/0.54                (k6_partfun1 @ sk_B)) @ 
% 0.35/0.54               sk_C)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['4', '15'])).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(cc2_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.54         ((v5_relat_1 @ X16 @ X18)
% 0.35/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.54  thf('19', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.35/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.54  thf(d19_relat_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ B ) =>
% 0.35/0.54       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      (![X2 : $i, X3 : $i]:
% 0.35/0.54         (~ (v5_relat_1 @ X2 @ X3)
% 0.35/0.54          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.35/0.54          | ~ (v1_relat_1 @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(cc2_relat_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.35/0.54          | (v1_relat_1 @ X0)
% 0.35/0.54          | ~ (v1_relat_1 @ X1))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.35/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.35/0.54  thf(fc6_relat_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.35/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.35/0.54  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.54  thf('27', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.35/0.54      inference('demod', [status(thm)], ['21', '26'])).
% 0.35/0.54  thf(t125_relat_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ B ) =>
% 0.35/0.54       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.35/0.54         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.35/0.54  thf('28', plain,
% 0.35/0.54      (![X8 : $i, X9 : $i]:
% 0.35/0.54         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.35/0.54          | ((k8_relat_1 @ X9 @ X8) = (X8))
% 0.35/0.54          | ~ (v1_relat_1 @ X8))),
% 0.35/0.54      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.35/0.54  thf('29', plain,
% 0.35/0.54      ((~ (v1_relat_1 @ sk_C) | ((k8_relat_1 @ sk_B @ sk_C) = (sk_C)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.54  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.54  thf('31', plain, (((k8_relat_1 @ sk_B @ sk_C) = (sk_C))),
% 0.35/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.35/0.54  thf('32', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(redefinition_r2_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.35/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.54       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.35/0.54  thf('33', plain,
% 0.35/0.54      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.35/0.54          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.35/0.54          | (r2_relset_1 @ X26 @ X27 @ X25 @ X28)
% 0.35/0.54          | ((X25) != (X28)))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.35/0.54  thf('34', plain,
% 0.35/0.54      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.35/0.54         ((r2_relset_1 @ X26 @ X27 @ X28 @ X28)
% 0.35/0.54          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.35/0.54      inference('simplify', [status(thm)], ['33'])).
% 0.35/0.54  thf('35', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.35/0.54      inference('sup-', [status(thm)], ['32', '34'])).
% 0.35/0.54  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.54  thf('37', plain,
% 0.35/0.54      (((r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 0.35/0.54         sk_C))),
% 0.35/0.54      inference('demod', [status(thm)], ['16', '31', '35', '36'])).
% 0.35/0.54  thf('38', plain,
% 0.35/0.54      (~
% 0.35/0.54       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.35/0.54         sk_C)) | 
% 0.35/0.54       ~
% 0.35/0.54       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 0.35/0.54         sk_C))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('39', plain,
% 0.35/0.54      (~
% 0.35/0.54       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.35/0.54         sk_C))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['37', '38'])).
% 0.35/0.54  thf('40', plain,
% 0.35/0.54      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.35/0.54          (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_relat_1 @ sk_A) @ sk_C) @ 
% 0.35/0.54          sk_C)),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['3', '39'])).
% 0.35/0.54  thf('41', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('42', plain,
% 0.35/0.54      (![X30 : $i]:
% 0.35/0.54         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 0.35/0.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.35/0.54      inference('demod', [status(thm)], ['5', '6'])).
% 0.35/0.54  thf('43', plain,
% 0.35/0.54      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.35/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.35/0.54          | ((k4_relset_1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22)
% 0.35/0.54              = (k5_relat_1 @ X19 @ X22)))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.35/0.54  thf('44', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.54         (((k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 0.35/0.54            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.35/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['42', '43'])).
% 0.35/0.54  thf('45', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ (k6_relat_1 @ X0) @ sk_C)
% 0.35/0.54           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_C))),
% 0.35/0.54      inference('sup-', [status(thm)], ['41', '44'])).
% 0.35/0.54  thf('46', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('47', plain,
% 0.35/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.54         ((v4_relat_1 @ X16 @ X17)
% 0.35/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.54  thf('48', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.35/0.54      inference('sup-', [status(thm)], ['46', '47'])).
% 0.35/0.54  thf(t209_relat_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.35/0.54       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.35/0.54  thf('49', plain,
% 0.35/0.54      (![X10 : $i, X11 : $i]:
% 0.35/0.54         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.35/0.54          | ~ (v4_relat_1 @ X10 @ X11)
% 0.35/0.54          | ~ (v1_relat_1 @ X10))),
% 0.35/0.54      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.35/0.54  thf('50', plain,
% 0.35/0.54      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['48', '49'])).
% 0.35/0.54  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.54  thf('52', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['50', '51'])).
% 0.35/0.54  thf(t87_relat_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ B ) =>
% 0.35/0.54       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.35/0.54  thf('53', plain,
% 0.35/0.54      (![X14 : $i, X15 : $i]:
% 0.35/0.54         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X14 @ X15)) @ X15)
% 0.35/0.54          | ~ (v1_relat_1 @ X14))),
% 0.35/0.54      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.35/0.54  thf('54', plain,
% 0.35/0.54      (((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A) | ~ (v1_relat_1 @ sk_C))),
% 0.35/0.54      inference('sup+', [status(thm)], ['52', '53'])).
% 0.35/0.54  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.54  thf('56', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.35/0.54      inference('demod', [status(thm)], ['54', '55'])).
% 0.35/0.54  thf(t77_relat_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ B ) =>
% 0.35/0.54       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.35/0.54         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.35/0.54  thf('57', plain,
% 0.35/0.54      (![X12 : $i, X13 : $i]:
% 0.35/0.54         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.35/0.54          | ((k5_relat_1 @ (k6_relat_1 @ X13) @ X12) = (X12))
% 0.35/0.54          | ~ (v1_relat_1 @ X12))),
% 0.35/0.54      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.35/0.54  thf('58', plain,
% 0.35/0.54      ((~ (v1_relat_1 @ sk_C)
% 0.35/0.54        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) = (sk_C)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['56', '57'])).
% 0.35/0.54  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.54  thf('60', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) = (sk_C))),
% 0.35/0.54      inference('demod', [status(thm)], ['58', '59'])).
% 0.35/0.54  thf('61', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.35/0.54      inference('sup-', [status(thm)], ['32', '34'])).
% 0.35/0.54  thf('62', plain, ($false),
% 0.35/0.54      inference('demod', [status(thm)], ['40', '45', '60', '61'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
