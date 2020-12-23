%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IlOdHST94D

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:52 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 319 expanded)
%              Number of leaves         :   36 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          : 1355 (5777 expanded)
%              Number of equality atoms :   38 ( 154 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

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
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X26 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
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
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('28',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X37 )
      | ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X36 ) @ X37 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('36',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('43',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X1 @ X0 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X1 @ X0 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('55',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('57',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','62'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('64',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('67',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['69','74'])).

thf('76',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('77',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['72','73'])).

thf('80',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('85',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['63','64','75','76','77','78','79','80','85'])).

thf('87',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('89',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('90',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['86','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IlOdHST94D
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:03:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.70  % Solved by: fo/fo7.sh
% 0.49/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.70  % done 406 iterations in 0.225s
% 0.49/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.70  % SZS output start Refutation
% 0.49/0.70  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.49/0.70  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.49/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.49/0.70  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.49/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.49/0.70  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.49/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.49/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.70  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.49/0.70  thf(sk_D_type, type, sk_D: $i).
% 0.49/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.49/0.70  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.49/0.70  thf(t24_funct_2, conjecture,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.49/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.70       ( ![D:$i]:
% 0.49/0.70         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.49/0.70             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.49/0.70           ( ( r2_relset_1 @
% 0.49/0.70               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.49/0.70               ( k6_partfun1 @ B ) ) =>
% 0.49/0.70             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.49/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.49/0.70        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.49/0.70            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.70          ( ![D:$i]:
% 0.49/0.70            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.49/0.70                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.49/0.70              ( ( r2_relset_1 @
% 0.49/0.70                  B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.49/0.70                  ( k6_partfun1 @ B ) ) =>
% 0.49/0.70                ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ) )),
% 0.49/0.70    inference('cnf.neg', [status(esa)], [t24_funct_2])).
% 0.49/0.70  thf('0', plain,
% 0.49/0.70      ((r2_relset_1 @ sk_B @ sk_B @ 
% 0.49/0.70        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.49/0.70        (k6_partfun1 @ sk_B))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(redefinition_k6_partfun1, axiom,
% 0.49/0.70    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.49/0.70  thf('1', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.49/0.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.49/0.70  thf('2', plain,
% 0.49/0.70      ((r2_relset_1 @ sk_B @ sk_B @ 
% 0.49/0.70        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.49/0.70        (k6_relat_1 @ sk_B))),
% 0.49/0.70      inference('demod', [status(thm)], ['0', '1'])).
% 0.49/0.70  thf('3', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('4', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(redefinition_k1_partfun1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.49/0.70     ( ( ( v1_funct_1 @ E ) & 
% 0.49/0.70         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.49/0.70         ( v1_funct_1 @ F ) & 
% 0.49/0.70         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.49/0.70       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.49/0.70  thf('5', plain,
% 0.49/0.70      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.49/0.70          | ~ (v1_funct_1 @ X29)
% 0.49/0.70          | ~ (v1_funct_1 @ X32)
% 0.49/0.70          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.49/0.70          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 0.49/0.70              = (k5_relat_1 @ X29 @ X32)))),
% 0.49/0.70      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.49/0.70  thf('6', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.49/0.70            = (k5_relat_1 @ sk_D @ X0))
% 0.49/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ sk_D))),
% 0.49/0.70      inference('sup-', [status(thm)], ['4', '5'])).
% 0.49/0.70  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('8', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.49/0.70            = (k5_relat_1 @ sk_D @ X0))
% 0.49/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.49/0.70          | ~ (v1_funct_1 @ X0))),
% 0.49/0.70      inference('demod', [status(thm)], ['6', '7'])).
% 0.49/0.70  thf('9', plain,
% 0.49/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.70        | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.49/0.70            = (k5_relat_1 @ sk_D @ sk_C)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['3', '8'])).
% 0.49/0.70  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('11', plain,
% 0.49/0.70      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.49/0.70         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.49/0.70      inference('demod', [status(thm)], ['9', '10'])).
% 0.49/0.70  thf('12', plain,
% 0.49/0.70      ((r2_relset_1 @ sk_B @ sk_B @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 0.49/0.70        (k6_relat_1 @ sk_B))),
% 0.49/0.70      inference('demod', [status(thm)], ['2', '11'])).
% 0.49/0.70  thf('13', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('14', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(dt_k1_partfun1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.49/0.70     ( ( ( v1_funct_1 @ E ) & 
% 0.49/0.70         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.49/0.70         ( v1_funct_1 @ F ) & 
% 0.49/0.70         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.49/0.70       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.49/0.70         ( m1_subset_1 @
% 0.49/0.70           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.49/0.70           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.49/0.70  thf('15', plain,
% 0.49/0.70      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.49/0.70          | ~ (v1_funct_1 @ X21)
% 0.49/0.70          | ~ (v1_funct_1 @ X24)
% 0.49/0.70          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.49/0.70          | (m1_subset_1 @ (k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24) @ 
% 0.49/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X26))))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.49/0.70  thf('16', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((m1_subset_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 0.49/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.49/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_funct_1 @ sk_D))),
% 0.49/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.49/0.70  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('18', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((m1_subset_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 0.49/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.49/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.49/0.70          | ~ (v1_funct_1 @ X1))),
% 0.49/0.70      inference('demod', [status(thm)], ['16', '17'])).
% 0.49/0.70  thf('19', plain,
% 0.49/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.70        | (m1_subset_1 @ 
% 0.49/0.70           (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.49/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.49/0.70      inference('sup-', [status(thm)], ['13', '18'])).
% 0.49/0.70  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('21', plain,
% 0.49/0.70      ((m1_subset_1 @ 
% 0.49/0.70        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.49/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['19', '20'])).
% 0.49/0.70  thf('22', plain,
% 0.49/0.70      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.49/0.70         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.49/0.70      inference('demod', [status(thm)], ['9', '10'])).
% 0.49/0.70  thf('23', plain,
% 0.49/0.70      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 0.49/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['21', '22'])).
% 0.49/0.70  thf(redefinition_r2_relset_1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.70     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.49/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.70       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.49/0.70  thf('24', plain,
% 0.49/0.70      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.49/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.49/0.70          | ((X17) = (X20))
% 0.49/0.70          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 0.49/0.70      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.49/0.70  thf('25', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (r2_relset_1 @ sk_B @ sk_B @ (k5_relat_1 @ sk_D @ sk_C) @ X0)
% 0.49/0.70          | ((k5_relat_1 @ sk_D @ sk_C) = (X0))
% 0.49/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.49/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.49/0.70  thf('26', plain,
% 0.49/0.70      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_B) @ 
% 0.49/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))
% 0.49/0.70        | ((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['12', '25'])).
% 0.49/0.70  thf(dt_k6_partfun1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( m1_subset_1 @
% 0.49/0.70         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.49/0.70       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.49/0.70  thf('27', plain,
% 0.49/0.70      (![X28 : $i]:
% 0.49/0.70         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 0.49/0.70          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.49/0.70  thf('28', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.49/0.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.49/0.70  thf('29', plain,
% 0.49/0.70      (![X28 : $i]:
% 0.49/0.70         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 0.49/0.70          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 0.49/0.70      inference('demod', [status(thm)], ['27', '28'])).
% 0.49/0.70  thf('30', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.49/0.70      inference('demod', [status(thm)], ['26', '29'])).
% 0.49/0.70  thf(d10_xboole_0, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.49/0.70  thf('31', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.49/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.49/0.70  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.49/0.70      inference('simplify', [status(thm)], ['31'])).
% 0.49/0.70  thf(t4_funct_2, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.70       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.49/0.70         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.49/0.70           ( m1_subset_1 @
% 0.49/0.70             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.49/0.70  thf('33', plain,
% 0.49/0.70      (![X36 : $i, X37 : $i]:
% 0.49/0.70         (~ (r1_tarski @ (k2_relat_1 @ X36) @ X37)
% 0.49/0.70          | (m1_subset_1 @ X36 @ 
% 0.49/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X36) @ X37)))
% 0.49/0.70          | ~ (v1_funct_1 @ X36)
% 0.49/0.70          | ~ (v1_relat_1 @ X36))),
% 0.49/0.70      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.49/0.70  thf('34', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | (m1_subset_1 @ X0 @ 
% 0.49/0.70             (k1_zfmisc_1 @ 
% 0.49/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.49/0.70      inference('sup-', [status(thm)], ['32', '33'])).
% 0.49/0.70  thf('35', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | (m1_subset_1 @ X0 @ 
% 0.49/0.70             (k1_zfmisc_1 @ 
% 0.49/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.49/0.70      inference('sup-', [status(thm)], ['32', '33'])).
% 0.49/0.70  thf('36', plain,
% 0.49/0.70      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.49/0.70          | ~ (v1_funct_1 @ X29)
% 0.49/0.70          | ~ (v1_funct_1 @ X32)
% 0.49/0.70          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.49/0.70          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 0.49/0.70              = (k5_relat_1 @ X29 @ X32)))),
% 0.49/0.70      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.49/0.70  thf('37', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.70         (~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 0.49/0.70              X0 @ X1) = (k5_relat_1 @ X0 @ X1))
% 0.49/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_funct_1 @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['35', '36'])).
% 0.49/0.70  thf('38', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.70         (~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 0.49/0.70          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 0.49/0.70              X0 @ X1) = (k5_relat_1 @ X0 @ X1))
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['37'])).
% 0.49/0.70  thf('39', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X1)
% 0.49/0.70          | ((k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 0.49/0.70              (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0)
% 0.49/0.70              = (k5_relat_1 @ X1 @ X0))
% 0.49/0.70          | ~ (v1_funct_1 @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['34', '38'])).
% 0.49/0.70  thf('40', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (((k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 0.49/0.70            (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0)
% 0.49/0.70            = (k5_relat_1 @ X1 @ X0))
% 0.49/0.70          | ~ (v1_relat_1 @ X1)
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['39'])).
% 0.49/0.70  thf('41', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | (m1_subset_1 @ X0 @ 
% 0.49/0.70             (k1_zfmisc_1 @ 
% 0.49/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.49/0.70      inference('sup-', [status(thm)], ['32', '33'])).
% 0.49/0.70  thf('42', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | (m1_subset_1 @ X0 @ 
% 0.49/0.70             (k1_zfmisc_1 @ 
% 0.49/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.49/0.70      inference('sup-', [status(thm)], ['32', '33'])).
% 0.49/0.70  thf('43', plain,
% 0.49/0.70      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.49/0.70          | ~ (v1_funct_1 @ X21)
% 0.49/0.70          | ~ (v1_funct_1 @ X24)
% 0.49/0.70          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.49/0.70          | (m1_subset_1 @ (k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24) @ 
% 0.49/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X26))))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.49/0.70  thf('44', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.70         (~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | (m1_subset_1 @ 
% 0.49/0.70             (k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X1 @ 
% 0.49/0.70              X0 @ X2) @ 
% 0.49/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.49/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 0.49/0.70          | ~ (v1_funct_1 @ X2)
% 0.49/0.70          | ~ (v1_funct_1 @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['42', '43'])).
% 0.49/0.70  thf('45', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.70         (~ (v1_funct_1 @ X2)
% 0.49/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 0.49/0.70          | (m1_subset_1 @ 
% 0.49/0.70             (k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X1 @ 
% 0.49/0.70              X0 @ X2) @ 
% 0.49/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['44'])).
% 0.49/0.70  thf('46', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X1)
% 0.49/0.70          | (m1_subset_1 @ 
% 0.49/0.70             (k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 0.49/0.70              (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0) @ 
% 0.49/0.70             (k1_zfmisc_1 @ 
% 0.49/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 0.49/0.70          | ~ (v1_funct_1 @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['41', '45'])).
% 0.49/0.70  thf('47', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((m1_subset_1 @ 
% 0.49/0.70           (k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 0.49/0.70            (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0) @ 
% 0.49/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 0.49/0.70          | ~ (v1_relat_1 @ X1)
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['46'])).
% 0.49/0.70  thf('48', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((m1_subset_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.49/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X1)
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X1))),
% 0.49/0.70      inference('sup+', [status(thm)], ['40', '47'])).
% 0.49/0.70  thf('49', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X1)
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | (m1_subset_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.49/0.70             (k1_zfmisc_1 @ 
% 0.49/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0)))))),
% 0.49/0.70      inference('simplify', [status(thm)], ['48'])).
% 0.49/0.70  thf(cc2_relat_1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( v1_relat_1 @ A ) =>
% 0.49/0.70       ( ![B:$i]:
% 0.49/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.49/0.70  thf('50', plain,
% 0.49/0.70      (![X3 : $i, X4 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.49/0.70          | (v1_relat_1 @ X3)
% 0.49/0.70          | ~ (v1_relat_1 @ X4))),
% 0.49/0.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.49/0.70  thf('51', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ 
% 0.49/0.70               (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 0.49/0.70          | (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['49', '50'])).
% 0.49/0.70  thf(fc6_relat_1, axiom,
% 0.49/0.70    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.49/0.70  thf('52', plain,
% 0.49/0.70      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.49/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.49/0.70  thf('53', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X1)
% 0.49/0.70          | (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.49/0.70      inference('demod', [status(thm)], ['51', '52'])).
% 0.49/0.70  thf('54', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X1)
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | (m1_subset_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.49/0.70             (k1_zfmisc_1 @ 
% 0.49/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0)))))),
% 0.49/0.70      inference('simplify', [status(thm)], ['48'])).
% 0.49/0.70  thf(cc2_relset_1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.49/0.70  thf('55', plain,
% 0.49/0.70      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.70         ((v5_relat_1 @ X11 @ X13)
% 0.49/0.70          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.49/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.49/0.70  thf('56', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X1)
% 0.49/0.70          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['54', '55'])).
% 0.49/0.70  thf(d19_relat_1, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( v1_relat_1 @ B ) =>
% 0.49/0.70       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.49/0.70  thf('57', plain,
% 0.49/0.70      (![X5 : $i, X6 : $i]:
% 0.49/0.70         (~ (v5_relat_1 @ X5 @ X6)
% 0.49/0.70          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.49/0.70          | ~ (v1_relat_1 @ X5))),
% 0.49/0.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.49/0.70  thf('58', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X1)
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.49/0.70          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.49/0.70             (k2_relat_1 @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['56', '57'])).
% 0.49/0.70  thf('59', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X1)
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.49/0.70             (k2_relat_1 @ X0))
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X1))),
% 0.49/0.70      inference('sup-', [status(thm)], ['53', '58'])).
% 0.49/0.70  thf('60', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.49/0.70           (k2_relat_1 @ X0))
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X1))),
% 0.49/0.70      inference('simplify', [status(thm)], ['59'])).
% 0.49/0.70  thf('61', plain,
% 0.49/0.70      (![X0 : $i, X2 : $i]:
% 0.49/0.70         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.49/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.49/0.70  thf('62', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X1)
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.49/0.70               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.49/0.70          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.49/0.70      inference('sup-', [status(thm)], ['60', '61'])).
% 0.49/0.70  thf('63', plain,
% 0.49/0.70      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_relat_1 @ (k6_relat_1 @ sk_B)))
% 0.49/0.70        | ((k2_relat_1 @ sk_C) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C)))
% 0.49/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.70        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.70        | ~ (v1_funct_1 @ sk_D)
% 0.49/0.70        | ~ (v1_relat_1 @ sk_D))),
% 0.49/0.70      inference('sup-', [status(thm)], ['30', '62'])).
% 0.49/0.70  thf(t71_relat_1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.49/0.70       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.49/0.70  thf('64', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.49/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.49/0.70  thf('65', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('66', plain,
% 0.49/0.70      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.70         ((v5_relat_1 @ X11 @ X13)
% 0.49/0.70          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.49/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.49/0.70  thf('67', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.49/0.70      inference('sup-', [status(thm)], ['65', '66'])).
% 0.49/0.70  thf('68', plain,
% 0.49/0.70      (![X5 : $i, X6 : $i]:
% 0.49/0.70         (~ (v5_relat_1 @ X5 @ X6)
% 0.49/0.70          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.49/0.70          | ~ (v1_relat_1 @ X5))),
% 0.49/0.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.49/0.70  thf('69', plain,
% 0.49/0.70      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.49/0.70      inference('sup-', [status(thm)], ['67', '68'])).
% 0.49/0.70  thf('70', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('71', plain,
% 0.49/0.70      (![X3 : $i, X4 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.49/0.70          | (v1_relat_1 @ X3)
% 0.49/0.70          | ~ (v1_relat_1 @ X4))),
% 0.49/0.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.49/0.70  thf('72', plain,
% 0.49/0.70      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.49/0.70      inference('sup-', [status(thm)], ['70', '71'])).
% 0.49/0.70  thf('73', plain,
% 0.49/0.70      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.49/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.49/0.70  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.70      inference('demod', [status(thm)], ['72', '73'])).
% 0.49/0.70  thf('75', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.49/0.70      inference('demod', [status(thm)], ['69', '74'])).
% 0.49/0.70  thf('76', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.49/0.70      inference('demod', [status(thm)], ['26', '29'])).
% 0.49/0.70  thf('77', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.49/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.49/0.70  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.70      inference('demod', [status(thm)], ['72', '73'])).
% 0.49/0.70  thf('80', plain, ((v1_funct_1 @ sk_D)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('81', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('82', plain,
% 0.49/0.70      (![X3 : $i, X4 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.49/0.70          | (v1_relat_1 @ X3)
% 0.49/0.70          | ~ (v1_relat_1 @ X4))),
% 0.49/0.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.49/0.70  thf('83', plain,
% 0.49/0.70      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.49/0.70      inference('sup-', [status(thm)], ['81', '82'])).
% 0.49/0.70  thf('84', plain,
% 0.49/0.70      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.49/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.49/0.70  thf('85', plain, ((v1_relat_1 @ sk_D)),
% 0.49/0.70      inference('demod', [status(thm)], ['83', '84'])).
% 0.49/0.70  thf('86', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.49/0.70      inference('demod', [status(thm)],
% 0.49/0.70                ['63', '64', '75', '76', '77', '78', '79', '80', '85'])).
% 0.49/0.70  thf('87', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('88', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(redefinition_k2_relset_1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.49/0.70  thf('89', plain,
% 0.49/0.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.70         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.49/0.70          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.49/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.49/0.70  thf('90', plain,
% 0.49/0.70      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.49/0.70      inference('sup-', [status(thm)], ['88', '89'])).
% 0.49/0.70  thf('91', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.49/0.70      inference('demod', [status(thm)], ['87', '90'])).
% 0.49/0.70  thf('92', plain, ($false),
% 0.49/0.70      inference('simplify_reflect-', [status(thm)], ['86', '91'])).
% 0.49/0.70  
% 0.49/0.70  % SZS output end Refutation
% 0.49/0.70  
% 0.49/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
