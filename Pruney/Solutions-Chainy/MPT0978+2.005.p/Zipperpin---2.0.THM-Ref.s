%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3QMODM7dL1

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:52 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 240 expanded)
%              Number of leaves         :   36 (  86 expanded)
%              Depth                    :   13
%              Number of atoms          :  864 (4370 expanded)
%              Number of equality atoms :   35 ( 127 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t24_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
             => ( ( k2_relset_1 @ A @ B @ C )
                = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X16 @ X17 @ X19 @ X20 @ X15 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ( v5_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['16','19','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('27',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k6_partfun1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('33',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 )
        = ( k5_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
      = ( k5_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('42',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( X30 = X33 )
      | ~ ( r2_relset_1 @ X31 @ X32 @ X30 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_B @ sk_B @ ( k5_relat_1 @ sk_D @ sk_C ) @ X0 )
      | ( ( k5_relat_1 @ sk_D @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('45',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('46',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('47',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['44','47'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('49',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('50',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('51',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('54',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('58',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('60',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['29','48','51','58','59','60'])).

thf('62',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('64',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('65',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3QMODM7dL1
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:48:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.54/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.77  % Solved by: fo/fo7.sh
% 0.54/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.77  % done 628 iterations in 0.341s
% 0.54/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.77  % SZS output start Refutation
% 0.54/0.77  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.77  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.54/0.77  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.77  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.54/0.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.77  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.54/0.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.77  thf(sk_D_type, type, sk_D: $i).
% 0.54/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.77  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.54/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.77  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.54/0.77  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.54/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.77  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.54/0.77  thf(t24_funct_2, conjecture,
% 0.54/0.77    (![A:$i,B:$i,C:$i]:
% 0.54/0.77     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.77       ( ![D:$i]:
% 0.54/0.77         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.54/0.77             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.54/0.77           ( ( r2_relset_1 @
% 0.54/0.77               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.54/0.77               ( k6_partfun1 @ B ) ) =>
% 0.54/0.77             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.54/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.77    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.77        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.77            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.77          ( ![D:$i]:
% 0.54/0.77            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.54/0.77                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.54/0.77              ( ( r2_relset_1 @
% 0.54/0.77                  B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.54/0.77                  ( k6_partfun1 @ B ) ) =>
% 0.54/0.77                ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ) )),
% 0.54/0.77    inference('cnf.neg', [status(esa)], [t24_funct_2])).
% 0.54/0.77  thf('0', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('1', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(dt_k4_relset_1, axiom,
% 0.54/0.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.54/0.77     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.54/0.77         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.54/0.77       ( m1_subset_1 @
% 0.54/0.77         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.54/0.77         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.54/0.77  thf('2', plain,
% 0.54/0.77      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.54/0.77          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.54/0.77          | (m1_subset_1 @ (k4_relset_1 @ X16 @ X17 @ X19 @ X20 @ X15 @ X18) @ 
% 0.54/0.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X20))))),
% 0.54/0.77      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.54/0.77  thf('3', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.77         ((m1_subset_1 @ (k4_relset_1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 0.54/0.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.54/0.77          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.54/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.77  thf('4', plain,
% 0.54/0.77      ((m1_subset_1 @ 
% 0.54/0.77        (k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.54/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['0', '3'])).
% 0.54/0.77  thf('5', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('6', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(redefinition_k4_relset_1, axiom,
% 0.54/0.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.54/0.77     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.54/0.77         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.54/0.77       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.54/0.77  thf('7', plain,
% 0.54/0.77      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.54/0.77          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.54/0.77          | ((k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 0.54/0.77              = (k5_relat_1 @ X24 @ X27)))),
% 0.54/0.77      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.54/0.77  thf('8', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.77         (((k4_relset_1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.54/0.77            = (k5_relat_1 @ sk_D @ X0))
% 0.54/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.54/0.77      inference('sup-', [status(thm)], ['6', '7'])).
% 0.54/0.77  thf('9', plain,
% 0.54/0.77      (((k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.54/0.77         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.54/0.77      inference('sup-', [status(thm)], ['5', '8'])).
% 0.54/0.77  thf('10', plain,
% 0.54/0.77      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 0.54/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.54/0.77      inference('demod', [status(thm)], ['4', '9'])).
% 0.54/0.77  thf(cc1_relset_1, axiom,
% 0.54/0.77    (![A:$i,B:$i,C:$i]:
% 0.54/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.77       ( v1_relat_1 @ C ) ))).
% 0.54/0.77  thf('11', plain,
% 0.54/0.77      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.54/0.77         ((v1_relat_1 @ X9)
% 0.54/0.77          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.54/0.77      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.54/0.77  thf('12', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_C))),
% 0.54/0.77      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.77  thf(t45_relat_1, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( v1_relat_1 @ A ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( v1_relat_1 @ B ) =>
% 0.54/0.77           ( r1_tarski @
% 0.54/0.77             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.54/0.77  thf('13', plain,
% 0.54/0.77      (![X5 : $i, X6 : $i]:
% 0.54/0.77         (~ (v1_relat_1 @ X5)
% 0.54/0.77          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 0.54/0.77             (k2_relat_1 @ X5))
% 0.54/0.77          | ~ (v1_relat_1 @ X6))),
% 0.54/0.77      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.54/0.77  thf(d19_relat_1, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( v1_relat_1 @ B ) =>
% 0.54/0.77       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.54/0.77  thf('14', plain,
% 0.54/0.77      (![X3 : $i, X4 : $i]:
% 0.54/0.77         (~ (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.54/0.77          | (v5_relat_1 @ X3 @ X4)
% 0.54/0.77          | ~ (v1_relat_1 @ X3))),
% 0.54/0.77      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.54/0.77  thf('15', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i]:
% 0.54/0.77         (~ (v1_relat_1 @ X1)
% 0.54/0.77          | ~ (v1_relat_1 @ X0)
% 0.54/0.77          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.54/0.77          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['13', '14'])).
% 0.54/0.77  thf('16', plain,
% 0.54/0.77      (((v5_relat_1 @ (k5_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.54/0.77        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.77        | ~ (v1_relat_1 @ sk_D))),
% 0.54/0.77      inference('sup-', [status(thm)], ['12', '15'])).
% 0.54/0.77  thf('17', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('18', plain,
% 0.54/0.77      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.54/0.77         ((v1_relat_1 @ X9)
% 0.54/0.77          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.54/0.77      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.54/0.77  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.77      inference('sup-', [status(thm)], ['17', '18'])).
% 0.54/0.77  thf('20', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('21', plain,
% 0.54/0.77      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.54/0.77         ((v1_relat_1 @ X9)
% 0.54/0.77          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.54/0.77      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.54/0.77  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 0.54/0.77      inference('sup-', [status(thm)], ['20', '21'])).
% 0.54/0.77  thf('23', plain,
% 0.54/0.77      ((v5_relat_1 @ (k5_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.54/0.77      inference('demod', [status(thm)], ['16', '19', '22'])).
% 0.54/0.77  thf('24', plain,
% 0.54/0.77      (![X3 : $i, X4 : $i]:
% 0.54/0.77         (~ (v5_relat_1 @ X3 @ X4)
% 0.54/0.77          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.54/0.77          | ~ (v1_relat_1 @ X3))),
% 0.54/0.77      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.54/0.77  thf('25', plain,
% 0.54/0.77      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_C))
% 0.54/0.77        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C)) @ 
% 0.54/0.77           (k2_relat_1 @ sk_C)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['23', '24'])).
% 0.54/0.77  thf('26', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_C))),
% 0.54/0.77      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.77  thf('27', plain,
% 0.54/0.77      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C)) @ 
% 0.54/0.77        (k2_relat_1 @ sk_C))),
% 0.54/0.77      inference('demod', [status(thm)], ['25', '26'])).
% 0.54/0.77  thf(d10_xboole_0, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.77  thf('28', plain,
% 0.54/0.77      (![X0 : $i, X2 : $i]:
% 0.54/0.77         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.77  thf('29', plain,
% 0.54/0.77      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.54/0.77           (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C)))
% 0.54/0.77        | ((k2_relat_1 @ sk_C) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C))))),
% 0.54/0.77      inference('sup-', [status(thm)], ['27', '28'])).
% 0.54/0.77  thf('30', plain,
% 0.54/0.77      ((r2_relset_1 @ sk_B @ sk_B @ 
% 0.54/0.77        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.54/0.77        (k6_partfun1 @ sk_B))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('31', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('32', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(redefinition_k1_partfun1, axiom,
% 0.54/0.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.54/0.77     ( ( ( v1_funct_1 @ E ) & 
% 0.54/0.77         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.54/0.77         ( v1_funct_1 @ F ) & 
% 0.54/0.77         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.54/0.77       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.54/0.77  thf('33', plain,
% 0.54/0.77      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.54/0.77          | ~ (v1_funct_1 @ X35)
% 0.54/0.77          | ~ (v1_funct_1 @ X38)
% 0.54/0.77          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.54/0.77          | ((k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38)
% 0.54/0.77              = (k5_relat_1 @ X35 @ X38)))),
% 0.54/0.77      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.54/0.77  thf('34', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.77         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.54/0.77            = (k5_relat_1 @ sk_D @ X0))
% 0.54/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.54/0.77          | ~ (v1_funct_1 @ X0)
% 0.54/0.77          | ~ (v1_funct_1 @ sk_D))),
% 0.54/0.77      inference('sup-', [status(thm)], ['32', '33'])).
% 0.54/0.77  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('36', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.77         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.54/0.77            = (k5_relat_1 @ sk_D @ X0))
% 0.54/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.54/0.77          | ~ (v1_funct_1 @ X0))),
% 0.54/0.77      inference('demod', [status(thm)], ['34', '35'])).
% 0.54/0.77  thf('37', plain,
% 0.54/0.77      ((~ (v1_funct_1 @ sk_C)
% 0.54/0.77        | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.54/0.77            = (k5_relat_1 @ sk_D @ sk_C)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['31', '36'])).
% 0.54/0.77  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('39', plain,
% 0.54/0.77      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.54/0.77         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.54/0.77      inference('demod', [status(thm)], ['37', '38'])).
% 0.54/0.77  thf('40', plain,
% 0.54/0.77      ((r2_relset_1 @ sk_B @ sk_B @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 0.54/0.77        (k6_partfun1 @ sk_B))),
% 0.54/0.77      inference('demod', [status(thm)], ['30', '39'])).
% 0.54/0.77  thf('41', plain,
% 0.54/0.77      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 0.54/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.54/0.77      inference('demod', [status(thm)], ['4', '9'])).
% 0.54/0.77  thf(redefinition_r2_relset_1, axiom,
% 0.54/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.77     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.54/0.77         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.77       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.54/0.77  thf('42', plain,
% 0.54/0.77      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.54/0.77          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.54/0.77          | ((X30) = (X33))
% 0.54/0.77          | ~ (r2_relset_1 @ X31 @ X32 @ X30 @ X33))),
% 0.54/0.77      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.54/0.77  thf('43', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (r2_relset_1 @ sk_B @ sk_B @ (k5_relat_1 @ sk_D @ sk_C) @ X0)
% 0.54/0.77          | ((k5_relat_1 @ sk_D @ sk_C) = (X0))
% 0.54/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.54/0.77      inference('sup-', [status(thm)], ['41', '42'])).
% 0.54/0.77  thf('44', plain,
% 0.54/0.77      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_B) @ 
% 0.54/0.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))
% 0.54/0.77        | ((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['40', '43'])).
% 0.54/0.77  thf(t29_relset_1, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( m1_subset_1 @
% 0.54/0.77       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.54/0.77  thf('45', plain,
% 0.54/0.77      (![X34 : $i]:
% 0.54/0.77         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 0.54/0.77          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 0.54/0.77      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.54/0.77  thf(redefinition_k6_partfun1, axiom,
% 0.54/0.77    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.54/0.77  thf('46', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.54/0.77      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.54/0.77  thf('47', plain,
% 0.54/0.77      (![X34 : $i]:
% 0.54/0.77         (m1_subset_1 @ (k6_partfun1 @ X34) @ 
% 0.54/0.77          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 0.54/0.77      inference('demod', [status(thm)], ['45', '46'])).
% 0.54/0.77  thf('48', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.54/0.77      inference('demod', [status(thm)], ['44', '47'])).
% 0.54/0.77  thf(t71_relat_1, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.54/0.77       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.54/0.77  thf('49', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.54/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.54/0.77  thf('50', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.54/0.77      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.54/0.77  thf('51', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 0.54/0.77      inference('demod', [status(thm)], ['49', '50'])).
% 0.54/0.77  thf('52', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(cc2_relset_1, axiom,
% 0.54/0.77    (![A:$i,B:$i,C:$i]:
% 0.54/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.77       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.77  thf('53', plain,
% 0.54/0.77      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.54/0.77         ((v5_relat_1 @ X12 @ X14)
% 0.54/0.77          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.54/0.77      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.77  thf('54', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.54/0.77      inference('sup-', [status(thm)], ['52', '53'])).
% 0.54/0.77  thf('55', plain,
% 0.54/0.77      (![X3 : $i, X4 : $i]:
% 0.54/0.77         (~ (v5_relat_1 @ X3 @ X4)
% 0.54/0.77          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.54/0.77          | ~ (v1_relat_1 @ X3))),
% 0.54/0.77      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.54/0.77  thf('56', plain,
% 0.54/0.77      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.54/0.77      inference('sup-', [status(thm)], ['54', '55'])).
% 0.54/0.77  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.77      inference('sup-', [status(thm)], ['17', '18'])).
% 0.54/0.77  thf('58', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.54/0.77      inference('demod', [status(thm)], ['56', '57'])).
% 0.54/0.77  thf('59', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.54/0.77      inference('demod', [status(thm)], ['44', '47'])).
% 0.54/0.77  thf('60', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 0.54/0.77      inference('demod', [status(thm)], ['49', '50'])).
% 0.54/0.77  thf('61', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.54/0.77      inference('demod', [status(thm)], ['29', '48', '51', '58', '59', '60'])).
% 0.54/0.77  thf('62', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('63', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(redefinition_k2_relset_1, axiom,
% 0.54/0.77    (![A:$i,B:$i,C:$i]:
% 0.54/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.77       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.54/0.77  thf('64', plain,
% 0.54/0.77      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.54/0.77         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.54/0.77          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.54/0.77      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.54/0.77  thf('65', plain,
% 0.54/0.77      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.54/0.77      inference('sup-', [status(thm)], ['63', '64'])).
% 0.54/0.77  thf('66', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.54/0.77      inference('demod', [status(thm)], ['62', '65'])).
% 0.54/0.77  thf('67', plain, ($false),
% 0.54/0.77      inference('simplify_reflect-', [status(thm)], ['61', '66'])).
% 0.54/0.77  
% 0.54/0.77  % SZS output end Refutation
% 0.54/0.77  
% 0.54/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
