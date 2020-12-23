%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TyuUqaSCLm

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:07 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  226 (1114 expanded)
%              Number of leaves         :   49 ( 353 expanded)
%              Depth                    :   29
%              Number of atoms          : 2167 (28182 expanded)
%              Number of equality atoms :  161 (1857 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ X50 @ ( k2_funct_1 @ X50 ) )
        = ( k6_partfun1 @ X51 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ X50 @ ( k2_funct_1 @ X50 ) )
        = ( k6_relat_1 @ X51 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('23',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('24',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('25',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
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

thf('28',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_relset_1 @ X37 @ X37 @ ( k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39 ) @ ( k6_partfun1 @ X37 ) )
      | ( ( k2_relset_1 @ X38 @ X37 @ X39 )
        = X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('29',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_relset_1 @ X37 @ X37 @ ( k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39 ) @ ( k6_relat_1 @ X37 ) )
      | ( ( k2_relset_1 @ X38 @ X37 @ X39 )
        = X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('37',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('38',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['35','39','40','41','42','43'])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['7','44'])).

thf('46',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','45','46','47'])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ! [E: $i] :
          ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
            & ( v1_funct_2 @ E @ B @ C )
            & ( v1_funct_1 @ E ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) )
           => ( ( ( v2_funct_1 @ E )
                & ( v2_funct_1 @ D ) )
              | ( ( B != k1_xboole_0 )
                & ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i] :
      ( ( zip_tseitin_1 @ C @ B )
     => ( ( C = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [E: $i,D: $i] :
      ( ( zip_tseitin_0 @ E @ D )
     => ( ( v2_funct_1 @ D )
        & ( v2_funct_1 @ E ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
              & ( ( k2_relset_1 @ A @ B @ D )
                = B ) )
           => ( ( zip_tseitin_1 @ C @ B )
              | ( zip_tseitin_0 @ E @ D ) ) ) ) ) )).

thf('54',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( zip_tseitin_0 @ X44 @ X47 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X48 @ X45 @ X45 @ X46 @ X47 @ X44 ) )
      | ( zip_tseitin_1 @ X46 @ X45 )
      | ( ( k2_relset_1 @ X48 @ X45 @ X47 )
       != X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X45 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('60',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','64'])).

thf('66',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('68',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v2_funct_1 @ X41 )
      | ~ ( zip_tseitin_0 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('72',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['51','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('76',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('83',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('84',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X9 @ X10 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('85',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['35','39','40','41','42','43'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('88',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('89',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('93',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['85','86','89','90','95','96','99'])).

thf('101',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('103',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('104',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k10_relat_1 @ X6 @ X7 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X6 ) @ X7 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('105',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('106',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['51','72'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('108',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('109',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['35','39','40','41','42','43'])).

thf('111',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['87','88'])).

thf('112',plain,
    ( ( sk_B
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_B
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['87','88'])).

thf('115',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( sk_B
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_A ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ( sk_B
      = ( k10_relat_1 @ sk_D @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['104','116'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['35','39','40','41','42','43'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('119',plain,(
    ! [X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k2_relat_1 @ X2 ) )
        = ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('120',plain,
    ( ( ( k10_relat_1 @ sk_D @ sk_A )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['87','88'])).

thf('122',plain,
    ( ( k10_relat_1 @ sk_D @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['87','88'])).

thf('124',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('126',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['117','122','123','124','125'])).

thf('127',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['103','126'])).

thf('128',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['73','128'])).

thf('130',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X9 @ X10 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('131',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['93','94'])).

thf('133',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('134',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['35','39','40','41','42','43'])).

thf('137',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k10_relat_1 @ X6 @ X7 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X6 ) @ X7 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('138',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('139',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ X50 @ ( k2_funct_1 @ X50 ) )
        = ( k6_relat_1 @ X51 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('141',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['141','142','143','144','145'])).

thf('147',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('151',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('153',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['93','94'])).

thf('154',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('155',plain,
    ( ( sk_A
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','152','153','154'])).

thf('156',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_A
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['138','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( sk_A
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,
    ( ( sk_A
      = ( k10_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['137','159'])).

thf('161',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['93','94'])).

thf('162',plain,(
    ! [X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k2_relat_1 @ X2 ) )
        = ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('163',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('165',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('167',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['160','165','166','167','168'])).

thf('170',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['87','88'])).

thf('172',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','135','136','169','170','171'])).

thf('173',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['173','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TyuUqaSCLm
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.67/1.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.67/1.92  % Solved by: fo/fo7.sh
% 1.67/1.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.67/1.92  % done 817 iterations in 1.464s
% 1.67/1.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.67/1.92  % SZS output start Refutation
% 1.67/1.92  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.67/1.92  thf(sk_C_type, type, sk_C: $i).
% 1.67/1.92  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.67/1.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.67/1.92  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.67/1.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.67/1.92  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.67/1.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.67/1.92  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.67/1.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.67/1.92  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.67/1.92  thf(sk_D_type, type, sk_D: $i).
% 1.67/1.92  thf(sk_B_type, type, sk_B: $i).
% 1.67/1.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.67/1.92  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.67/1.92  thf(sk_A_type, type, sk_A: $i).
% 1.67/1.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.67/1.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.67/1.92  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.67/1.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.67/1.92  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.67/1.92  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.67/1.92  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.67/1.92  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.67/1.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.67/1.92  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.67/1.92  thf(t36_funct_2, conjecture,
% 1.67/1.92    (![A:$i,B:$i,C:$i]:
% 1.67/1.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.67/1.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.67/1.92       ( ![D:$i]:
% 1.67/1.92         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.67/1.92             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.67/1.92           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.67/1.92               ( r2_relset_1 @
% 1.67/1.92                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.67/1.92                 ( k6_partfun1 @ A ) ) & 
% 1.67/1.92               ( v2_funct_1 @ C ) ) =>
% 1.67/1.92             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.67/1.92               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.67/1.92  thf(zf_stmt_0, negated_conjecture,
% 1.67/1.92    (~( ![A:$i,B:$i,C:$i]:
% 1.67/1.92        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.67/1.92            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.67/1.92          ( ![D:$i]:
% 1.67/1.92            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.67/1.92                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.67/1.92              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.67/1.92                  ( r2_relset_1 @
% 1.67/1.92                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.67/1.92                    ( k6_partfun1 @ A ) ) & 
% 1.67/1.92                  ( v2_funct_1 @ C ) ) =>
% 1.67/1.92                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.67/1.92                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.67/1.92    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.67/1.92  thf('0', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf(t35_funct_2, axiom,
% 1.67/1.92    (![A:$i,B:$i,C:$i]:
% 1.67/1.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.67/1.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.67/1.92       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.67/1.92         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.67/1.92           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.67/1.92             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.67/1.92  thf('1', plain,
% 1.67/1.92      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.67/1.92         (((X49) = (k1_xboole_0))
% 1.67/1.92          | ~ (v1_funct_1 @ X50)
% 1.67/1.92          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 1.67/1.92          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 1.67/1.92          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_partfun1 @ X51))
% 1.67/1.92          | ~ (v2_funct_1 @ X50)
% 1.67/1.92          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 1.67/1.92      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.67/1.92  thf(redefinition_k6_partfun1, axiom,
% 1.67/1.92    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.67/1.92  thf('2', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.67/1.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.67/1.92  thf('3', plain,
% 1.67/1.92      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.67/1.92         (((X49) = (k1_xboole_0))
% 1.67/1.92          | ~ (v1_funct_1 @ X50)
% 1.67/1.92          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 1.67/1.92          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 1.67/1.92          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_relat_1 @ X51))
% 1.67/1.92          | ~ (v2_funct_1 @ X50)
% 1.67/1.92          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 1.67/1.92      inference('demod', [status(thm)], ['1', '2'])).
% 1.67/1.92  thf('4', plain,
% 1.67/1.92      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.67/1.92        | ~ (v2_funct_1 @ sk_D)
% 1.67/1.92        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.67/1.92        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.67/1.92        | ~ (v1_funct_1 @ sk_D)
% 1.67/1.92        | ((sk_A) = (k1_xboole_0)))),
% 1.67/1.92      inference('sup-', [status(thm)], ['0', '3'])).
% 1.67/1.92  thf('5', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf(redefinition_k2_relset_1, axiom,
% 1.67/1.92    (![A:$i,B:$i,C:$i]:
% 1.67/1.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.67/1.92       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.67/1.92  thf('6', plain,
% 1.67/1.92      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.67/1.92         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 1.67/1.92          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.67/1.92      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.67/1.92  thf('7', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.67/1.92      inference('sup-', [status(thm)], ['5', '6'])).
% 1.67/1.92  thf('8', plain,
% 1.67/1.92      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.67/1.92        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.67/1.92        (k6_partfun1 @ sk_A))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('9', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.67/1.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.67/1.92  thf('10', plain,
% 1.67/1.92      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.67/1.92        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.67/1.92        (k6_relat_1 @ sk_A))),
% 1.67/1.92      inference('demod', [status(thm)], ['8', '9'])).
% 1.67/1.92  thf('11', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('12', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf(dt_k1_partfun1, axiom,
% 1.67/1.92    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.67/1.92     ( ( ( v1_funct_1 @ E ) & 
% 1.67/1.92         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.67/1.92         ( v1_funct_1 @ F ) & 
% 1.67/1.92         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.67/1.92       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.67/1.92         ( m1_subset_1 @
% 1.67/1.92           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.67/1.92           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.67/1.92  thf('13', plain,
% 1.67/1.92      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.67/1.92         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.67/1.92          | ~ (v1_funct_1 @ X21)
% 1.67/1.92          | ~ (v1_funct_1 @ X24)
% 1.67/1.92          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.67/1.92          | (m1_subset_1 @ (k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24) @ 
% 1.67/1.92             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X26))))),
% 1.67/1.92      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.67/1.92  thf('14', plain,
% 1.67/1.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.92         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.67/1.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.67/1.92          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.67/1.92          | ~ (v1_funct_1 @ X1)
% 1.67/1.92          | ~ (v1_funct_1 @ sk_C))),
% 1.67/1.92      inference('sup-', [status(thm)], ['12', '13'])).
% 1.67/1.92  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('16', plain,
% 1.67/1.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.92         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.67/1.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.67/1.92          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.67/1.92          | ~ (v1_funct_1 @ X1))),
% 1.67/1.92      inference('demod', [status(thm)], ['14', '15'])).
% 1.67/1.92  thf('17', plain,
% 1.67/1.92      ((~ (v1_funct_1 @ sk_D)
% 1.67/1.92        | (m1_subset_1 @ 
% 1.67/1.92           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.67/1.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.67/1.92      inference('sup-', [status(thm)], ['11', '16'])).
% 1.67/1.92  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('19', plain,
% 1.67/1.92      ((m1_subset_1 @ 
% 1.67/1.92        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.67/1.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.67/1.92      inference('demod', [status(thm)], ['17', '18'])).
% 1.67/1.92  thf(redefinition_r2_relset_1, axiom,
% 1.67/1.92    (![A:$i,B:$i,C:$i,D:$i]:
% 1.67/1.92     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.67/1.92         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.67/1.92       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.67/1.92  thf('20', plain,
% 1.67/1.92      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.67/1.92         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.67/1.92          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.67/1.92          | ((X17) = (X20))
% 1.67/1.92          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 1.67/1.92      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.67/1.92  thf('21', plain,
% 1.67/1.92      (![X0 : $i]:
% 1.67/1.92         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.67/1.92             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.67/1.92          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.67/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.67/1.92      inference('sup-', [status(thm)], ['19', '20'])).
% 1.67/1.92  thf('22', plain,
% 1.67/1.92      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.67/1.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.67/1.92        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.67/1.92            = (k6_relat_1 @ sk_A)))),
% 1.67/1.92      inference('sup-', [status(thm)], ['10', '21'])).
% 1.67/1.92  thf(dt_k6_partfun1, axiom,
% 1.67/1.92    (![A:$i]:
% 1.67/1.92     ( ( m1_subset_1 @
% 1.67/1.92         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.67/1.92       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.67/1.92  thf('23', plain,
% 1.67/1.92      (![X28 : $i]:
% 1.67/1.92         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 1.67/1.92          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 1.67/1.92      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.67/1.92  thf('24', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.67/1.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.67/1.92  thf('25', plain,
% 1.67/1.92      (![X28 : $i]:
% 1.67/1.92         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 1.67/1.92          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 1.67/1.92      inference('demod', [status(thm)], ['23', '24'])).
% 1.67/1.92  thf('26', plain,
% 1.67/1.92      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.67/1.92         = (k6_relat_1 @ sk_A))),
% 1.67/1.92      inference('demod', [status(thm)], ['22', '25'])).
% 1.67/1.92  thf('27', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf(t24_funct_2, axiom,
% 1.67/1.92    (![A:$i,B:$i,C:$i]:
% 1.67/1.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.67/1.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.67/1.92       ( ![D:$i]:
% 1.67/1.92         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.67/1.92             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.67/1.92           ( ( r2_relset_1 @
% 1.67/1.92               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.67/1.92               ( k6_partfun1 @ B ) ) =>
% 1.67/1.92             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.67/1.92  thf('28', plain,
% 1.67/1.92      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.67/1.92         (~ (v1_funct_1 @ X36)
% 1.67/1.92          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 1.67/1.92          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.67/1.92          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 1.67/1.92               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 1.67/1.92               (k6_partfun1 @ X37))
% 1.67/1.92          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 1.67/1.92          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 1.67/1.92          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 1.67/1.92          | ~ (v1_funct_1 @ X39))),
% 1.67/1.92      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.67/1.92  thf('29', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.67/1.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.67/1.92  thf('30', plain,
% 1.67/1.92      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.67/1.92         (~ (v1_funct_1 @ X36)
% 1.67/1.92          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 1.67/1.92          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.67/1.92          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 1.67/1.92               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 1.67/1.92               (k6_relat_1 @ X37))
% 1.67/1.92          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 1.67/1.92          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 1.67/1.92          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 1.67/1.92          | ~ (v1_funct_1 @ X39))),
% 1.67/1.92      inference('demod', [status(thm)], ['28', '29'])).
% 1.67/1.92  thf('31', plain,
% 1.67/1.92      (![X0 : $i]:
% 1.67/1.92         (~ (v1_funct_1 @ X0)
% 1.67/1.92          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.67/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.67/1.92          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.67/1.92          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.67/1.92               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.67/1.92               (k6_relat_1 @ sk_A))
% 1.67/1.92          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.67/1.92          | ~ (v1_funct_1 @ sk_C))),
% 1.67/1.92      inference('sup-', [status(thm)], ['27', '30'])).
% 1.67/1.92  thf('32', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('34', plain,
% 1.67/1.92      (![X0 : $i]:
% 1.67/1.92         (~ (v1_funct_1 @ X0)
% 1.67/1.92          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.67/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.67/1.92          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.67/1.92          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.67/1.92               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.67/1.92               (k6_relat_1 @ sk_A)))),
% 1.67/1.92      inference('demod', [status(thm)], ['31', '32', '33'])).
% 1.67/1.92  thf('35', plain,
% 1.67/1.92      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.67/1.92           (k6_relat_1 @ sk_A))
% 1.67/1.92        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.67/1.92        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.67/1.92        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.67/1.92        | ~ (v1_funct_1 @ sk_D))),
% 1.67/1.92      inference('sup-', [status(thm)], ['26', '34'])).
% 1.67/1.92  thf('36', plain,
% 1.67/1.92      (![X28 : $i]:
% 1.67/1.92         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 1.67/1.92          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 1.67/1.92      inference('demod', [status(thm)], ['23', '24'])).
% 1.67/1.92  thf('37', plain,
% 1.67/1.92      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.67/1.92         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.67/1.92          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.67/1.92          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 1.67/1.92          | ((X17) != (X20)))),
% 1.67/1.92      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.67/1.92  thf('38', plain,
% 1.67/1.92      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.67/1.92         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 1.67/1.92          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.67/1.92      inference('simplify', [status(thm)], ['37'])).
% 1.67/1.92  thf('39', plain,
% 1.67/1.92      (![X0 : $i]:
% 1.67/1.92         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.67/1.92      inference('sup-', [status(thm)], ['36', '38'])).
% 1.67/1.92  thf('40', plain,
% 1.67/1.92      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.67/1.92      inference('sup-', [status(thm)], ['5', '6'])).
% 1.67/1.92  thf('41', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('42', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('44', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.67/1.92      inference('demod', [status(thm)], ['35', '39', '40', '41', '42', '43'])).
% 1.67/1.92  thf('45', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 1.67/1.92      inference('demod', [status(thm)], ['7', '44'])).
% 1.67/1.92  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('48', plain,
% 1.67/1.92      ((((sk_A) != (sk_A))
% 1.67/1.92        | ~ (v2_funct_1 @ sk_D)
% 1.67/1.92        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.67/1.92        | ((sk_A) = (k1_xboole_0)))),
% 1.67/1.92      inference('demod', [status(thm)], ['4', '45', '46', '47'])).
% 1.67/1.92  thf('49', plain,
% 1.67/1.92      ((((sk_A) = (k1_xboole_0))
% 1.67/1.92        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.67/1.92        | ~ (v2_funct_1 @ sk_D))),
% 1.67/1.92      inference('simplify', [status(thm)], ['48'])).
% 1.67/1.92  thf('50', plain, (((sk_A) != (k1_xboole_0))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('51', plain,
% 1.67/1.92      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.67/1.92        | ~ (v2_funct_1 @ sk_D))),
% 1.67/1.92      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 1.67/1.92  thf('52', plain,
% 1.67/1.92      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.67/1.92         = (k6_relat_1 @ sk_A))),
% 1.67/1.92      inference('demod', [status(thm)], ['22', '25'])).
% 1.67/1.92  thf('53', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf(t30_funct_2, axiom,
% 1.67/1.92    (![A:$i,B:$i,C:$i,D:$i]:
% 1.67/1.92     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.67/1.92         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.67/1.92       ( ![E:$i]:
% 1.67/1.92         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.67/1.92             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.67/1.92           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.67/1.92               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.67/1.92             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.67/1.92               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.67/1.92  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.67/1.92  thf(zf_stmt_2, axiom,
% 1.67/1.92    (![C:$i,B:$i]:
% 1.67/1.92     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.67/1.92       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.67/1.92  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.67/1.92  thf(zf_stmt_4, axiom,
% 1.67/1.92    (![E:$i,D:$i]:
% 1.67/1.92     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.67/1.92  thf(zf_stmt_5, axiom,
% 1.67/1.92    (![A:$i,B:$i,C:$i,D:$i]:
% 1.67/1.92     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.67/1.92         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.67/1.92       ( ![E:$i]:
% 1.67/1.92         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.67/1.92             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.67/1.92           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.67/1.92               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.67/1.92             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.67/1.92  thf('54', plain,
% 1.67/1.92      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.67/1.92         (~ (v1_funct_1 @ X44)
% 1.67/1.92          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 1.67/1.92          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 1.67/1.92          | (zip_tseitin_0 @ X44 @ X47)
% 1.67/1.92          | ~ (v2_funct_1 @ (k1_partfun1 @ X48 @ X45 @ X45 @ X46 @ X47 @ X44))
% 1.67/1.92          | (zip_tseitin_1 @ X46 @ X45)
% 1.67/1.92          | ((k2_relset_1 @ X48 @ X45 @ X47) != (X45))
% 1.67/1.92          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X45)))
% 1.67/1.92          | ~ (v1_funct_2 @ X47 @ X48 @ X45)
% 1.67/1.92          | ~ (v1_funct_1 @ X47))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.67/1.92  thf('55', plain,
% 1.67/1.92      (![X0 : $i, X1 : $i]:
% 1.67/1.92         (~ (v1_funct_1 @ X0)
% 1.67/1.92          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.67/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.67/1.92          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.67/1.92          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.67/1.92          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.67/1.92          | (zip_tseitin_0 @ sk_D @ X0)
% 1.67/1.92          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.67/1.92          | ~ (v1_funct_1 @ sk_D))),
% 1.67/1.92      inference('sup-', [status(thm)], ['53', '54'])).
% 1.67/1.92  thf('56', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('58', plain,
% 1.67/1.92      (![X0 : $i, X1 : $i]:
% 1.67/1.92         (~ (v1_funct_1 @ X0)
% 1.67/1.92          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.67/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.67/1.92          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.67/1.92          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.67/1.92          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.67/1.92          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.67/1.92      inference('demod', [status(thm)], ['55', '56', '57'])).
% 1.67/1.92  thf('59', plain,
% 1.67/1.92      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.67/1.92        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.67/1.92        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.67/1.92        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.67/1.92        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.67/1.92        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.67/1.92        | ~ (v1_funct_1 @ sk_C))),
% 1.67/1.92      inference('sup-', [status(thm)], ['52', '58'])).
% 1.67/1.92  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 1.67/1.92  thf('60', plain, (![X8 : $i]: (v2_funct_1 @ (k6_relat_1 @ X8))),
% 1.67/1.92      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.67/1.92  thf('61', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('62', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('63', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('65', plain,
% 1.67/1.92      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.67/1.92        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.67/1.92        | ((sk_B) != (sk_B)))),
% 1.67/1.92      inference('demod', [status(thm)], ['59', '60', '61', '62', '63', '64'])).
% 1.67/1.92  thf('66', plain,
% 1.67/1.92      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.67/1.92      inference('simplify', [status(thm)], ['65'])).
% 1.67/1.92  thf('67', plain,
% 1.67/1.92      (![X42 : $i, X43 : $i]:
% 1.67/1.92         (((X42) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X42 @ X43))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.67/1.92  thf('68', plain,
% 1.67/1.92      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.67/1.92      inference('sup-', [status(thm)], ['66', '67'])).
% 1.67/1.92  thf('69', plain, (((sk_A) != (k1_xboole_0))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('70', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.67/1.92      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 1.67/1.92  thf('71', plain,
% 1.67/1.92      (![X40 : $i, X41 : $i]:
% 1.67/1.92         ((v2_funct_1 @ X41) | ~ (zip_tseitin_0 @ X41 @ X40))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.67/1.92  thf('72', plain, ((v2_funct_1 @ sk_D)),
% 1.67/1.92      inference('sup-', [status(thm)], ['70', '71'])).
% 1.67/1.92  thf('73', plain,
% 1.67/1.92      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 1.67/1.92      inference('demod', [status(thm)], ['51', '72'])).
% 1.67/1.92  thf('74', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('75', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf(redefinition_k1_partfun1, axiom,
% 1.67/1.92    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.67/1.92     ( ( ( v1_funct_1 @ E ) & 
% 1.67/1.92         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.67/1.92         ( v1_funct_1 @ F ) & 
% 1.67/1.92         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.67/1.92       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.67/1.92  thf('76', plain,
% 1.67/1.92      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.67/1.92         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.67/1.92          | ~ (v1_funct_1 @ X29)
% 1.67/1.92          | ~ (v1_funct_1 @ X32)
% 1.67/1.92          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.67/1.92          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 1.67/1.92              = (k5_relat_1 @ X29 @ X32)))),
% 1.67/1.92      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.67/1.92  thf('77', plain,
% 1.67/1.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.92         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.67/1.92            = (k5_relat_1 @ sk_C @ X0))
% 1.67/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.67/1.92          | ~ (v1_funct_1 @ X0)
% 1.67/1.92          | ~ (v1_funct_1 @ sk_C))),
% 1.67/1.92      inference('sup-', [status(thm)], ['75', '76'])).
% 1.67/1.92  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('79', plain,
% 1.67/1.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.92         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.67/1.92            = (k5_relat_1 @ sk_C @ X0))
% 1.67/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.67/1.92          | ~ (v1_funct_1 @ X0))),
% 1.67/1.92      inference('demod', [status(thm)], ['77', '78'])).
% 1.67/1.92  thf('80', plain,
% 1.67/1.92      ((~ (v1_funct_1 @ sk_D)
% 1.67/1.92        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.67/1.92            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.67/1.92      inference('sup-', [status(thm)], ['74', '79'])).
% 1.67/1.92  thf('81', plain, ((v1_funct_1 @ sk_D)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('82', plain,
% 1.67/1.92      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.67/1.92         = (k6_relat_1 @ sk_A))),
% 1.67/1.92      inference('demod', [status(thm)], ['22', '25'])).
% 1.67/1.92  thf('83', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.67/1.92      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.67/1.92  thf(t64_funct_1, axiom,
% 1.67/1.92    (![A:$i]:
% 1.67/1.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.67/1.92       ( ![B:$i]:
% 1.67/1.92         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.67/1.92           ( ( ( v2_funct_1 @ A ) & 
% 1.67/1.92               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.67/1.92               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.67/1.92             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.67/1.92  thf('84', plain,
% 1.67/1.92      (![X9 : $i, X10 : $i]:
% 1.67/1.92         (~ (v1_relat_1 @ X9)
% 1.67/1.92          | ~ (v1_funct_1 @ X9)
% 1.67/1.92          | ((X9) = (k2_funct_1 @ X10))
% 1.67/1.92          | ((k5_relat_1 @ X9 @ X10) != (k6_relat_1 @ (k2_relat_1 @ X10)))
% 1.67/1.92          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 1.67/1.92          | ~ (v2_funct_1 @ X10)
% 1.67/1.92          | ~ (v1_funct_1 @ X10)
% 1.67/1.92          | ~ (v1_relat_1 @ X10))),
% 1.67/1.92      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.67/1.92  thf('85', plain,
% 1.67/1.92      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 1.67/1.92        | ~ (v1_relat_1 @ sk_D)
% 1.67/1.92        | ~ (v1_funct_1 @ sk_D)
% 1.67/1.92        | ~ (v2_funct_1 @ sk_D)
% 1.67/1.92        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.67/1.92        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.67/1.92        | ~ (v1_funct_1 @ sk_C)
% 1.67/1.92        | ~ (v1_relat_1 @ sk_C))),
% 1.67/1.92      inference('sup-', [status(thm)], ['83', '84'])).
% 1.67/1.92  thf('86', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.67/1.92      inference('demod', [status(thm)], ['35', '39', '40', '41', '42', '43'])).
% 1.67/1.92  thf('87', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf(cc1_relset_1, axiom,
% 1.67/1.92    (![A:$i,B:$i,C:$i]:
% 1.67/1.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.67/1.92       ( v1_relat_1 @ C ) ))).
% 1.67/1.92  thf('88', plain,
% 1.67/1.92      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.67/1.92         ((v1_relat_1 @ X11)
% 1.67/1.92          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.67/1.92      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.67/1.92  thf('89', plain, ((v1_relat_1 @ sk_D)),
% 1.67/1.92      inference('sup-', [status(thm)], ['87', '88'])).
% 1.67/1.92  thf('90', plain, ((v1_funct_1 @ sk_D)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('91', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('92', plain,
% 1.67/1.92      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.67/1.92         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 1.67/1.92          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.67/1.92      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.67/1.92  thf('93', plain,
% 1.67/1.92      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.67/1.92      inference('sup-', [status(thm)], ['91', '92'])).
% 1.67/1.92  thf('94', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('95', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.67/1.92      inference('sup+', [status(thm)], ['93', '94'])).
% 1.67/1.92  thf('96', plain, ((v1_funct_1 @ sk_C)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('97', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('98', plain,
% 1.67/1.92      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.67/1.92         ((v1_relat_1 @ X11)
% 1.67/1.92          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.67/1.92      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.67/1.92  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 1.67/1.92      inference('sup-', [status(thm)], ['97', '98'])).
% 1.67/1.92  thf('100', plain,
% 1.67/1.92      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 1.67/1.92        | ~ (v2_funct_1 @ sk_D)
% 1.67/1.92        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.67/1.92        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.67/1.92      inference('demod', [status(thm)],
% 1.67/1.92                ['85', '86', '89', '90', '95', '96', '99'])).
% 1.67/1.92  thf('101', plain,
% 1.67/1.92      ((((sk_C) = (k2_funct_1 @ sk_D))
% 1.67/1.92        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.67/1.92        | ~ (v2_funct_1 @ sk_D))),
% 1.67/1.92      inference('simplify', [status(thm)], ['100'])).
% 1.67/1.92  thf('102', plain, ((v2_funct_1 @ sk_D)),
% 1.67/1.92      inference('sup-', [status(thm)], ['70', '71'])).
% 1.67/1.92  thf('103', plain,
% 1.67/1.92      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 1.67/1.92      inference('demod', [status(thm)], ['101', '102'])).
% 1.67/1.92  thf(t155_funct_1, axiom,
% 1.67/1.92    (![A:$i,B:$i]:
% 1.67/1.92     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.67/1.92       ( ( v2_funct_1 @ B ) =>
% 1.67/1.92         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 1.67/1.92  thf('104', plain,
% 1.67/1.92      (![X6 : $i, X7 : $i]:
% 1.67/1.92         (~ (v2_funct_1 @ X6)
% 1.67/1.92          | ((k10_relat_1 @ X6 @ X7) = (k9_relat_1 @ (k2_funct_1 @ X6) @ X7))
% 1.67/1.92          | ~ (v1_funct_1 @ X6)
% 1.67/1.92          | ~ (v1_relat_1 @ X6))),
% 1.67/1.92      inference('cnf', [status(esa)], [t155_funct_1])).
% 1.67/1.92  thf(dt_k2_funct_1, axiom,
% 1.67/1.92    (![A:$i]:
% 1.67/1.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.67/1.92       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.67/1.92         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.67/1.92  thf('105', plain,
% 1.67/1.92      (![X5 : $i]:
% 1.67/1.92         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 1.67/1.92          | ~ (v1_funct_1 @ X5)
% 1.67/1.92          | ~ (v1_relat_1 @ X5))),
% 1.67/1.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.67/1.92  thf('106', plain,
% 1.67/1.92      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 1.67/1.92      inference('demod', [status(thm)], ['51', '72'])).
% 1.67/1.92  thf(t160_relat_1, axiom,
% 1.67/1.92    (![A:$i]:
% 1.67/1.92     ( ( v1_relat_1 @ A ) =>
% 1.67/1.92       ( ![B:$i]:
% 1.67/1.92         ( ( v1_relat_1 @ B ) =>
% 1.67/1.92           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.67/1.92             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.67/1.92  thf('107', plain,
% 1.67/1.92      (![X0 : $i, X1 : $i]:
% 1.67/1.92         (~ (v1_relat_1 @ X0)
% 1.67/1.92          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.67/1.92              = (k9_relat_1 @ X0 @ (k2_relat_1 @ X1)))
% 1.67/1.92          | ~ (v1_relat_1 @ X1))),
% 1.67/1.92      inference('cnf', [status(esa)], [t160_relat_1])).
% 1.67/1.92  thf('108', plain,
% 1.67/1.92      ((((k2_relat_1 @ (k6_relat_1 @ sk_B))
% 1.67/1.92          = (k9_relat_1 @ (k2_funct_1 @ sk_D) @ (k2_relat_1 @ sk_D)))
% 1.67/1.92        | ~ (v1_relat_1 @ sk_D)
% 1.67/1.92        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 1.67/1.92      inference('sup+', [status(thm)], ['106', '107'])).
% 1.67/1.92  thf(t71_relat_1, axiom,
% 1.67/1.92    (![A:$i]:
% 1.67/1.92     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.67/1.92       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.67/1.92  thf('109', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 1.67/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.67/1.92  thf('110', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.67/1.92      inference('demod', [status(thm)], ['35', '39', '40', '41', '42', '43'])).
% 1.67/1.92  thf('111', plain, ((v1_relat_1 @ sk_D)),
% 1.67/1.92      inference('sup-', [status(thm)], ['87', '88'])).
% 1.67/1.92  thf('112', plain,
% 1.67/1.92      ((((sk_B) = (k9_relat_1 @ (k2_funct_1 @ sk_D) @ sk_A))
% 1.67/1.92        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 1.67/1.92      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 1.67/1.92  thf('113', plain,
% 1.67/1.92      ((~ (v1_relat_1 @ sk_D)
% 1.67/1.92        | ~ (v1_funct_1 @ sk_D)
% 1.67/1.92        | ((sk_B) = (k9_relat_1 @ (k2_funct_1 @ sk_D) @ sk_A)))),
% 1.67/1.92      inference('sup-', [status(thm)], ['105', '112'])).
% 1.67/1.92  thf('114', plain, ((v1_relat_1 @ sk_D)),
% 1.67/1.92      inference('sup-', [status(thm)], ['87', '88'])).
% 1.67/1.92  thf('115', plain, ((v1_funct_1 @ sk_D)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('116', plain, (((sk_B) = (k9_relat_1 @ (k2_funct_1 @ sk_D) @ sk_A))),
% 1.67/1.92      inference('demod', [status(thm)], ['113', '114', '115'])).
% 1.67/1.92  thf('117', plain,
% 1.67/1.92      ((((sk_B) = (k10_relat_1 @ sk_D @ sk_A))
% 1.67/1.92        | ~ (v1_relat_1 @ sk_D)
% 1.67/1.92        | ~ (v1_funct_1 @ sk_D)
% 1.67/1.92        | ~ (v2_funct_1 @ sk_D))),
% 1.67/1.92      inference('sup+', [status(thm)], ['104', '116'])).
% 1.67/1.92  thf('118', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.67/1.92      inference('demod', [status(thm)], ['35', '39', '40', '41', '42', '43'])).
% 1.67/1.92  thf(t169_relat_1, axiom,
% 1.67/1.92    (![A:$i]:
% 1.67/1.92     ( ( v1_relat_1 @ A ) =>
% 1.67/1.92       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.67/1.92  thf('119', plain,
% 1.67/1.92      (![X2 : $i]:
% 1.67/1.92         (((k10_relat_1 @ X2 @ (k2_relat_1 @ X2)) = (k1_relat_1 @ X2))
% 1.67/1.92          | ~ (v1_relat_1 @ X2))),
% 1.67/1.92      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.67/1.92  thf('120', plain,
% 1.67/1.92      ((((k10_relat_1 @ sk_D @ sk_A) = (k1_relat_1 @ sk_D))
% 1.67/1.92        | ~ (v1_relat_1 @ sk_D))),
% 1.67/1.92      inference('sup+', [status(thm)], ['118', '119'])).
% 1.67/1.92  thf('121', plain, ((v1_relat_1 @ sk_D)),
% 1.67/1.92      inference('sup-', [status(thm)], ['87', '88'])).
% 1.67/1.92  thf('122', plain, (((k10_relat_1 @ sk_D @ sk_A) = (k1_relat_1 @ sk_D))),
% 1.67/1.92      inference('demod', [status(thm)], ['120', '121'])).
% 1.67/1.92  thf('123', plain, ((v1_relat_1 @ sk_D)),
% 1.67/1.92      inference('sup-', [status(thm)], ['87', '88'])).
% 1.67/1.92  thf('124', plain, ((v1_funct_1 @ sk_D)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('125', plain, ((v2_funct_1 @ sk_D)),
% 1.67/1.92      inference('sup-', [status(thm)], ['70', '71'])).
% 1.67/1.92  thf('126', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.67/1.92      inference('demod', [status(thm)], ['117', '122', '123', '124', '125'])).
% 1.67/1.92  thf('127', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 1.67/1.92      inference('demod', [status(thm)], ['103', '126'])).
% 1.67/1.92  thf('128', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.67/1.92      inference('simplify', [status(thm)], ['127'])).
% 1.67/1.92  thf('129', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 1.67/1.92      inference('demod', [status(thm)], ['73', '128'])).
% 1.67/1.92  thf('130', plain,
% 1.67/1.92      (![X9 : $i, X10 : $i]:
% 1.67/1.92         (~ (v1_relat_1 @ X9)
% 1.67/1.92          | ~ (v1_funct_1 @ X9)
% 1.67/1.92          | ((X9) = (k2_funct_1 @ X10))
% 1.67/1.92          | ((k5_relat_1 @ X9 @ X10) != (k6_relat_1 @ (k2_relat_1 @ X10)))
% 1.67/1.92          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 1.67/1.92          | ~ (v2_funct_1 @ X10)
% 1.67/1.92          | ~ (v1_funct_1 @ X10)
% 1.67/1.92          | ~ (v1_relat_1 @ X10))),
% 1.67/1.92      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.67/1.92  thf('131', plain,
% 1.67/1.92      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 1.67/1.92        | ~ (v1_relat_1 @ sk_C)
% 1.67/1.92        | ~ (v1_funct_1 @ sk_C)
% 1.67/1.92        | ~ (v2_funct_1 @ sk_C)
% 1.67/1.92        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_C))
% 1.67/1.92        | ((sk_D) = (k2_funct_1 @ sk_C))
% 1.67/1.92        | ~ (v1_funct_1 @ sk_D)
% 1.67/1.92        | ~ (v1_relat_1 @ sk_D))),
% 1.67/1.92      inference('sup-', [status(thm)], ['129', '130'])).
% 1.67/1.92  thf('132', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.67/1.92      inference('sup+', [status(thm)], ['93', '94'])).
% 1.67/1.92  thf('133', plain, ((v1_relat_1 @ sk_C)),
% 1.67/1.92      inference('sup-', [status(thm)], ['97', '98'])).
% 1.67/1.92  thf('134', plain, ((v1_funct_1 @ sk_C)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('135', plain, ((v2_funct_1 @ sk_C)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('136', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.67/1.92      inference('demod', [status(thm)], ['35', '39', '40', '41', '42', '43'])).
% 1.67/1.92  thf('137', plain,
% 1.67/1.92      (![X6 : $i, X7 : $i]:
% 1.67/1.92         (~ (v2_funct_1 @ X6)
% 1.67/1.92          | ((k10_relat_1 @ X6 @ X7) = (k9_relat_1 @ (k2_funct_1 @ X6) @ X7))
% 1.67/1.92          | ~ (v1_funct_1 @ X6)
% 1.67/1.92          | ~ (v1_relat_1 @ X6))),
% 1.67/1.92      inference('cnf', [status(esa)], [t155_funct_1])).
% 1.67/1.92  thf('138', plain,
% 1.67/1.92      (![X5 : $i]:
% 1.67/1.92         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 1.67/1.92          | ~ (v1_funct_1 @ X5)
% 1.67/1.92          | ~ (v1_relat_1 @ X5))),
% 1.67/1.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.67/1.92  thf('139', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('140', plain,
% 1.67/1.92      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.67/1.92         (((X49) = (k1_xboole_0))
% 1.67/1.92          | ~ (v1_funct_1 @ X50)
% 1.67/1.92          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 1.67/1.92          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 1.67/1.92          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_relat_1 @ X51))
% 1.67/1.92          | ~ (v2_funct_1 @ X50)
% 1.67/1.92          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 1.67/1.92      inference('demod', [status(thm)], ['1', '2'])).
% 1.67/1.92  thf('141', plain,
% 1.67/1.92      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.67/1.92        | ~ (v2_funct_1 @ sk_C)
% 1.67/1.92        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.67/1.92        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.67/1.92        | ~ (v1_funct_1 @ sk_C)
% 1.67/1.92        | ((sk_B) = (k1_xboole_0)))),
% 1.67/1.92      inference('sup-', [status(thm)], ['139', '140'])).
% 1.67/1.92  thf('142', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('143', plain, ((v2_funct_1 @ sk_C)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('144', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('145', plain, ((v1_funct_1 @ sk_C)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('146', plain,
% 1.67/1.92      ((((sk_B) != (sk_B))
% 1.67/1.92        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.67/1.92        | ((sk_B) = (k1_xboole_0)))),
% 1.67/1.92      inference('demod', [status(thm)], ['141', '142', '143', '144', '145'])).
% 1.67/1.92  thf('147', plain,
% 1.67/1.92      ((((sk_B) = (k1_xboole_0))
% 1.67/1.92        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 1.67/1.92      inference('simplify', [status(thm)], ['146'])).
% 1.67/1.92  thf('148', plain, (((sk_B) != (k1_xboole_0))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('149', plain,
% 1.67/1.92      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 1.67/1.92      inference('simplify_reflect-', [status(thm)], ['147', '148'])).
% 1.67/1.92  thf('150', plain,
% 1.67/1.92      (![X0 : $i, X1 : $i]:
% 1.67/1.92         (~ (v1_relat_1 @ X0)
% 1.67/1.92          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.67/1.92              = (k9_relat_1 @ X0 @ (k2_relat_1 @ X1)))
% 1.67/1.92          | ~ (v1_relat_1 @ X1))),
% 1.67/1.92      inference('cnf', [status(esa)], [t160_relat_1])).
% 1.67/1.92  thf('151', plain,
% 1.67/1.92      ((((k2_relat_1 @ (k6_relat_1 @ sk_A))
% 1.67/1.92          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))
% 1.67/1.92        | ~ (v1_relat_1 @ sk_C)
% 1.67/1.92        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.67/1.92      inference('sup+', [status(thm)], ['149', '150'])).
% 1.67/1.92  thf('152', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 1.67/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.67/1.92  thf('153', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.67/1.92      inference('sup+', [status(thm)], ['93', '94'])).
% 1.67/1.92  thf('154', plain, ((v1_relat_1 @ sk_C)),
% 1.67/1.92      inference('sup-', [status(thm)], ['97', '98'])).
% 1.67/1.92  thf('155', plain,
% 1.67/1.92      ((((sk_A) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))
% 1.67/1.92        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.67/1.92      inference('demod', [status(thm)], ['151', '152', '153', '154'])).
% 1.67/1.92  thf('156', plain,
% 1.67/1.92      ((~ (v1_relat_1 @ sk_C)
% 1.67/1.92        | ~ (v1_funct_1 @ sk_C)
% 1.67/1.92        | ((sk_A) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)))),
% 1.67/1.92      inference('sup-', [status(thm)], ['138', '155'])).
% 1.67/1.92  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 1.67/1.92      inference('sup-', [status(thm)], ['97', '98'])).
% 1.67/1.92  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('159', plain, (((sk_A) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 1.67/1.92      inference('demod', [status(thm)], ['156', '157', '158'])).
% 1.67/1.92  thf('160', plain,
% 1.67/1.92      ((((sk_A) = (k10_relat_1 @ sk_C @ sk_B))
% 1.67/1.92        | ~ (v1_relat_1 @ sk_C)
% 1.67/1.92        | ~ (v1_funct_1 @ sk_C)
% 1.67/1.92        | ~ (v2_funct_1 @ sk_C))),
% 1.67/1.92      inference('sup+', [status(thm)], ['137', '159'])).
% 1.67/1.92  thf('161', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.67/1.92      inference('sup+', [status(thm)], ['93', '94'])).
% 1.67/1.92  thf('162', plain,
% 1.67/1.92      (![X2 : $i]:
% 1.67/1.92         (((k10_relat_1 @ X2 @ (k2_relat_1 @ X2)) = (k1_relat_1 @ X2))
% 1.67/1.92          | ~ (v1_relat_1 @ X2))),
% 1.67/1.92      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.67/1.92  thf('163', plain,
% 1.67/1.92      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 1.67/1.92        | ~ (v1_relat_1 @ sk_C))),
% 1.67/1.92      inference('sup+', [status(thm)], ['161', '162'])).
% 1.67/1.92  thf('164', plain, ((v1_relat_1 @ sk_C)),
% 1.67/1.92      inference('sup-', [status(thm)], ['97', '98'])).
% 1.67/1.92  thf('165', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 1.67/1.92      inference('demod', [status(thm)], ['163', '164'])).
% 1.67/1.92  thf('166', plain, ((v1_relat_1 @ sk_C)),
% 1.67/1.92      inference('sup-', [status(thm)], ['97', '98'])).
% 1.67/1.92  thf('167', plain, ((v1_funct_1 @ sk_C)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('168', plain, ((v2_funct_1 @ sk_C)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('169', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.67/1.92      inference('demod', [status(thm)], ['160', '165', '166', '167', '168'])).
% 1.67/1.92  thf('170', plain, ((v1_funct_1 @ sk_D)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('171', plain, ((v1_relat_1 @ sk_D)),
% 1.67/1.92      inference('sup-', [status(thm)], ['87', '88'])).
% 1.67/1.92  thf('172', plain,
% 1.67/1.92      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 1.67/1.92        | ((sk_A) != (sk_A))
% 1.67/1.92        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.67/1.92      inference('demod', [status(thm)],
% 1.67/1.92                ['131', '132', '133', '134', '135', '136', '169', '170', '171'])).
% 1.67/1.92  thf('173', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.67/1.92      inference('simplify', [status(thm)], ['172'])).
% 1.67/1.92  thf('174', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('175', plain, ($false),
% 1.67/1.92      inference('simplify_reflect-', [status(thm)], ['173', '174'])).
% 1.67/1.92  
% 1.67/1.92  % SZS output end Refutation
% 1.67/1.92  
% 1.67/1.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
