%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zmwbEDGWxn

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:53 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 261 expanded)
%              Number of leaves         :   38 (  94 expanded)
%              Depth                    :   13
%              Number of atoms          :  943 (4441 expanded)
%              Number of equality atoms :   42 ( 142 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

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
    r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k6_partfun1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 )
        = ( k5_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
      = ( k5_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('23',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_B @ sk_B @ ( k5_relat_1 @ sk_D @ sk_C ) @ X0 )
      | ( ( k5_relat_1 @ sk_D @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('27',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('28',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','29'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('32',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t120_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
          = A ) ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X6 @ ( k2_relat_1 @ X7 ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) )
        = X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t120_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ) )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('46',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('56',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ( ( k8_relat_1 @ X9 @ X8 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k8_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('62',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('63',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('69',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['42','43','60','61','62','63','64','69'])).

thf('71',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('73',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('74',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zmwbEDGWxn
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.84/1.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.05  % Solved by: fo/fo7.sh
% 0.84/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.05  % done 573 iterations in 0.609s
% 0.84/1.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.05  % SZS output start Refutation
% 0.84/1.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.05  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.84/1.05  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.84/1.05  thf(sk_C_type, type, sk_C: $i).
% 0.84/1.05  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.84/1.05  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.84/1.05  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.84/1.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.84/1.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.05  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.84/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.05  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.84/1.05  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.05  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.84/1.05  thf(sk_D_type, type, sk_D: $i).
% 0.84/1.05  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.84/1.05  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.84/1.05  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.84/1.05  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.84/1.05  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.84/1.05  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.84/1.05  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.84/1.05  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.84/1.05  thf(t24_funct_2, conjecture,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.84/1.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.05       ( ![D:$i]:
% 0.84/1.05         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.84/1.05             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.84/1.05           ( ( r2_relset_1 @
% 0.84/1.05               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.84/1.05               ( k6_partfun1 @ B ) ) =>
% 0.84/1.05             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.84/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.05    (~( ![A:$i,B:$i,C:$i]:
% 0.84/1.05        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.84/1.05            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.05          ( ![D:$i]:
% 0.84/1.05            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.84/1.05                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.84/1.05              ( ( r2_relset_1 @
% 0.84/1.05                  B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.84/1.05                  ( k6_partfun1 @ B ) ) =>
% 0.84/1.05                ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ) )),
% 0.84/1.05    inference('cnf.neg', [status(esa)], [t24_funct_2])).
% 0.84/1.05  thf('0', plain,
% 0.84/1.05      ((r2_relset_1 @ sk_B @ sk_B @ 
% 0.84/1.05        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.84/1.05        (k6_partfun1 @ sk_B))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(redefinition_k6_partfun1, axiom,
% 0.84/1.05    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.84/1.05  thf('1', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.84/1.05      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.84/1.05  thf('2', plain,
% 0.84/1.05      ((r2_relset_1 @ sk_B @ sk_B @ 
% 0.84/1.05        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.84/1.05        (k6_relat_1 @ sk_B))),
% 0.84/1.05      inference('demod', [status(thm)], ['0', '1'])).
% 0.84/1.05  thf('3', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('4', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(redefinition_k1_partfun1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.84/1.05     ( ( ( v1_funct_1 @ E ) & 
% 0.84/1.05         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.84/1.05         ( v1_funct_1 @ F ) & 
% 0.84/1.05         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.84/1.05       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.84/1.05  thf('5', plain,
% 0.84/1.05      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.84/1.05         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.84/1.05          | ~ (v1_funct_1 @ X32)
% 0.84/1.05          | ~ (v1_funct_1 @ X35)
% 0.84/1.05          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.84/1.05          | ((k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)
% 0.84/1.05              = (k5_relat_1 @ X32 @ X35)))),
% 0.84/1.05      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.84/1.05  thf('6', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.84/1.05            = (k5_relat_1 @ sk_D @ X0))
% 0.84/1.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.84/1.05          | ~ (v1_funct_1 @ X0)
% 0.84/1.05          | ~ (v1_funct_1 @ sk_D))),
% 0.84/1.05      inference('sup-', [status(thm)], ['4', '5'])).
% 0.84/1.05  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('8', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.84/1.05            = (k5_relat_1 @ sk_D @ X0))
% 0.84/1.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.84/1.05          | ~ (v1_funct_1 @ X0))),
% 0.84/1.05      inference('demod', [status(thm)], ['6', '7'])).
% 0.84/1.05  thf('9', plain,
% 0.84/1.05      ((~ (v1_funct_1 @ sk_C)
% 0.84/1.05        | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.84/1.05            = (k5_relat_1 @ sk_D @ sk_C)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['3', '8'])).
% 0.84/1.05  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('11', plain,
% 0.84/1.05      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.84/1.05         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.84/1.05      inference('demod', [status(thm)], ['9', '10'])).
% 0.84/1.05  thf('12', plain,
% 0.84/1.05      ((r2_relset_1 @ sk_B @ sk_B @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 0.84/1.05        (k6_relat_1 @ sk_B))),
% 0.84/1.05      inference('demod', [status(thm)], ['2', '11'])).
% 0.84/1.05  thf('13', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('14', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(dt_k1_partfun1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.84/1.05     ( ( ( v1_funct_1 @ E ) & 
% 0.84/1.05         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.84/1.05         ( v1_funct_1 @ F ) & 
% 0.84/1.05         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.84/1.05       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.84/1.05         ( m1_subset_1 @
% 0.84/1.05           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.84/1.05           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.84/1.05  thf('15', plain,
% 0.84/1.05      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.84/1.05         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.84/1.05          | ~ (v1_funct_1 @ X24)
% 0.84/1.05          | ~ (v1_funct_1 @ X27)
% 0.84/1.05          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.84/1.05          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 0.84/1.05             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 0.84/1.05      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.84/1.05  thf('16', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         ((m1_subset_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 0.84/1.05           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.84/1.05          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.84/1.05          | ~ (v1_funct_1 @ X1)
% 0.84/1.05          | ~ (v1_funct_1 @ sk_D))),
% 0.84/1.05      inference('sup-', [status(thm)], ['14', '15'])).
% 0.84/1.05  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('18', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         ((m1_subset_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 0.84/1.05           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.84/1.05          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.84/1.05          | ~ (v1_funct_1 @ X1))),
% 0.84/1.05      inference('demod', [status(thm)], ['16', '17'])).
% 0.84/1.05  thf('19', plain,
% 0.84/1.05      ((~ (v1_funct_1 @ sk_C)
% 0.84/1.05        | (m1_subset_1 @ 
% 0.84/1.05           (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.84/1.05           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['13', '18'])).
% 0.84/1.05  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('21', plain,
% 0.84/1.05      ((m1_subset_1 @ 
% 0.84/1.05        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.84/1.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.84/1.05      inference('demod', [status(thm)], ['19', '20'])).
% 0.84/1.05  thf('22', plain,
% 0.84/1.05      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.84/1.05         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.84/1.05      inference('demod', [status(thm)], ['9', '10'])).
% 0.84/1.05  thf('23', plain,
% 0.84/1.05      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 0.84/1.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.84/1.05      inference('demod', [status(thm)], ['21', '22'])).
% 0.84/1.05  thf(redefinition_r2_relset_1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.05     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.84/1.05         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.05       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.84/1.05  thf('24', plain,
% 0.84/1.05      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.84/1.05         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.84/1.05          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.84/1.05          | ((X20) = (X23))
% 0.84/1.05          | ~ (r2_relset_1 @ X21 @ X22 @ X20 @ X23))),
% 0.84/1.05      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.84/1.05  thf('25', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_relset_1 @ sk_B @ sk_B @ (k5_relat_1 @ sk_D @ sk_C) @ X0)
% 0.84/1.05          | ((k5_relat_1 @ sk_D @ sk_C) = (X0))
% 0.84/1.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['23', '24'])).
% 0.84/1.05  thf('26', plain,
% 0.84/1.05      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_B) @ 
% 0.84/1.05           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))
% 0.84/1.05        | ((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['12', '25'])).
% 0.84/1.05  thf(dt_k6_partfun1, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( m1_subset_1 @
% 0.84/1.05         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.84/1.05       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.84/1.05  thf('27', plain,
% 0.84/1.05      (![X31 : $i]:
% 0.84/1.05         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 0.84/1.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.84/1.05      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.84/1.05  thf('28', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.84/1.05      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.84/1.05  thf('29', plain,
% 0.84/1.05      (![X31 : $i]:
% 0.84/1.05         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 0.84/1.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.84/1.05      inference('demod', [status(thm)], ['27', '28'])).
% 0.84/1.05  thf('30', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.84/1.05      inference('demod', [status(thm)], ['26', '29'])).
% 0.84/1.05  thf(t45_relat_1, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ A ) =>
% 0.84/1.05       ( ![B:$i]:
% 0.84/1.05         ( ( v1_relat_1 @ B ) =>
% 0.84/1.05           ( r1_tarski @
% 0.84/1.05             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.84/1.05  thf('31', plain,
% 0.84/1.05      (![X10 : $i, X11 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X10)
% 0.84/1.05          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X11 @ X10)) @ 
% 0.84/1.05             (k2_relat_1 @ X10))
% 0.84/1.05          | ~ (v1_relat_1 @ X11))),
% 0.84/1.05      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.84/1.05  thf(t71_relat_1, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.84/1.05       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.84/1.05  thf('32', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.84/1.05      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.84/1.05  thf(t120_relat_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ B ) =>
% 0.84/1.05       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.84/1.05         ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) = ( A ) ) ) ))).
% 0.84/1.05  thf('33', plain,
% 0.84/1.05      (![X6 : $i, X7 : $i]:
% 0.84/1.05         (~ (r1_tarski @ X6 @ (k2_relat_1 @ X7))
% 0.84/1.05          | ((k2_relat_1 @ (k8_relat_1 @ X6 @ X7)) = (X6))
% 0.84/1.05          | ~ (v1_relat_1 @ X7))),
% 0.84/1.05      inference('cnf', [status(esa)], [t120_relat_1])).
% 0.84/1.05  thf('34', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (~ (r1_tarski @ X1 @ X0)
% 0.84/1.05          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.84/1.05          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) = (X1)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['32', '33'])).
% 0.84/1.05  thf('35', plain,
% 0.84/1.05      (![X31 : $i]:
% 0.84/1.05         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 0.84/1.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.84/1.05      inference('demod', [status(thm)], ['27', '28'])).
% 0.84/1.05  thf(cc2_relat_1, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ A ) =>
% 0.84/1.05       ( ![B:$i]:
% 0.84/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.84/1.05  thf('36', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.84/1.05          | (v1_relat_1 @ X0)
% 0.84/1.05          | ~ (v1_relat_1 @ X1))),
% 0.84/1.05      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.84/1.05  thf('37', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 0.84/1.05          | (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['35', '36'])).
% 0.84/1.05  thf(fc6_relat_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.84/1.05  thf('38', plain,
% 0.84/1.05      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.84/1.05      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.84/1.05  thf('39', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.84/1.05      inference('demod', [status(thm)], ['37', '38'])).
% 0.84/1.05  thf('40', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (~ (r1_tarski @ X1 @ X0)
% 0.84/1.05          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) = (X1)))),
% 0.84/1.05      inference('demod', [status(thm)], ['34', '39'])).
% 0.84/1.05  thf('41', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X1)
% 0.84/1.05          | ~ (v1_relat_1 @ X0)
% 0.84/1.05          | ((k2_relat_1 @ 
% 0.84/1.05              (k8_relat_1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.84/1.05               (k6_relat_1 @ (k2_relat_1 @ X0))))
% 0.84/1.05              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['31', '40'])).
% 0.84/1.05  thf('42', plain,
% 0.84/1.05      ((((k2_relat_1 @ 
% 0.84/1.05          (k8_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ sk_B)) @ 
% 0.84/1.05           (k6_relat_1 @ (k2_relat_1 @ sk_C))))
% 0.84/1.05          = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C)))
% 0.84/1.05        | ~ (v1_relat_1 @ sk_C)
% 0.84/1.05        | ~ (v1_relat_1 @ sk_D))),
% 0.84/1.05      inference('sup+', [status(thm)], ['30', '41'])).
% 0.84/1.05  thf('43', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.84/1.05      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.84/1.05  thf('44', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(cc2_relset_1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.05       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.84/1.05  thf('45', plain,
% 0.84/1.05      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.84/1.05         ((v5_relat_1 @ X14 @ X16)
% 0.84/1.05          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.84/1.05      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.84/1.05  thf('46', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.84/1.05      inference('sup-', [status(thm)], ['44', '45'])).
% 0.84/1.05  thf(d19_relat_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ B ) =>
% 0.84/1.05       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.84/1.05  thf('47', plain,
% 0.84/1.05      (![X2 : $i, X3 : $i]:
% 0.84/1.05         (~ (v5_relat_1 @ X2 @ X3)
% 0.84/1.05          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.84/1.05          | ~ (v1_relat_1 @ X2))),
% 0.84/1.05      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.84/1.05  thf('48', plain,
% 0.84/1.05      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.84/1.05      inference('sup-', [status(thm)], ['46', '47'])).
% 0.84/1.05  thf('49', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('50', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.84/1.05          | (v1_relat_1 @ X0)
% 0.84/1.05          | ~ (v1_relat_1 @ X1))),
% 0.84/1.05      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.84/1.05  thf('51', plain,
% 0.84/1.05      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.84/1.05      inference('sup-', [status(thm)], ['49', '50'])).
% 0.84/1.05  thf('52', plain,
% 0.84/1.05      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.84/1.05      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.84/1.05  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.05      inference('demod', [status(thm)], ['51', '52'])).
% 0.84/1.05  thf('54', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.84/1.05      inference('demod', [status(thm)], ['48', '53'])).
% 0.84/1.05  thf('55', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.84/1.05      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.84/1.05  thf(t125_relat_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ B ) =>
% 0.84/1.05       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.84/1.05         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.84/1.05  thf('56', plain,
% 0.84/1.05      (![X8 : $i, X9 : $i]:
% 0.84/1.05         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.84/1.05          | ((k8_relat_1 @ X9 @ X8) = (X8))
% 0.84/1.05          | ~ (v1_relat_1 @ X8))),
% 0.84/1.05      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.84/1.05  thf('57', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (~ (r1_tarski @ X0 @ X1)
% 0.84/1.05          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.84/1.05          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['55', '56'])).
% 0.84/1.05  thf('58', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.84/1.05      inference('demod', [status(thm)], ['37', '38'])).
% 0.84/1.05  thf('59', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (~ (r1_tarski @ X0 @ X1)
% 0.84/1.05          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.84/1.05      inference('demod', [status(thm)], ['57', '58'])).
% 0.84/1.05  thf('60', plain,
% 0.84/1.05      (((k8_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.84/1.05         = (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['54', '59'])).
% 0.84/1.05  thf('61', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.84/1.05      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.84/1.05  thf('62', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.84/1.05      inference('demod', [status(thm)], ['26', '29'])).
% 0.84/1.05  thf('63', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.84/1.05      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.84/1.05  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.05      inference('demod', [status(thm)], ['51', '52'])).
% 0.84/1.05  thf('65', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('66', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.84/1.05          | (v1_relat_1 @ X0)
% 0.84/1.05          | ~ (v1_relat_1 @ X1))),
% 0.84/1.05      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.84/1.05  thf('67', plain,
% 0.84/1.05      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.84/1.05      inference('sup-', [status(thm)], ['65', '66'])).
% 0.84/1.05  thf('68', plain,
% 0.84/1.05      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.84/1.05      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.84/1.05  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 0.84/1.05      inference('demod', [status(thm)], ['67', '68'])).
% 0.84/1.05  thf('70', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.84/1.05      inference('demod', [status(thm)],
% 0.84/1.05                ['42', '43', '60', '61', '62', '63', '64', '69'])).
% 0.84/1.05  thf('71', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('72', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(redefinition_k2_relset_1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.05       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.84/1.05  thf('73', plain,
% 0.84/1.05      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.84/1.05         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.84/1.05          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.84/1.05      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.84/1.05  thf('74', plain,
% 0.84/1.05      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.84/1.05      inference('sup-', [status(thm)], ['72', '73'])).
% 0.84/1.05  thf('75', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.84/1.05      inference('demod', [status(thm)], ['71', '74'])).
% 0.84/1.05  thf('76', plain, ($false),
% 0.84/1.05      inference('simplify_reflect-', [status(thm)], ['70', '75'])).
% 0.84/1.05  
% 0.84/1.05  % SZS output end Refutation
% 0.84/1.05  
% 0.84/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
