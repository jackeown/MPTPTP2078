%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jnDGYrOKhW

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:06 EST 2020

% Result     : Theorem 35.40s
% Output     : Refutation 35.40s
% Verified   : 
% Statistics : Number of formulae       :  298 (1131 expanded)
%              Number of leaves         :   46 ( 353 expanded)
%              Depth                    :   20
%              Number of atoms          : 3411 (28356 expanded)
%              Number of equality atoms :  218 (1933 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

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
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X49 ) @ X49 )
        = ( k6_partfun1 @ X48 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X49 ) @ X49 )
        = ( k6_relat_1 @ X48 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_relat_1 @ sk_A ) )
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X25 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 ) ) ),
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
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('24',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('25',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38 ) @ ( k6_partfun1 @ X36 ) )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('29',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38 ) @ ( k6_relat_1 @ X36 ) )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
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
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('37',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 )
      | ( X16 != X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('38',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','45','46','47'])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_relat_1 @ sk_A ) )
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( zip_tseitin_0 @ X43 @ X46 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X47 @ X44 @ X44 @ X45 @ X46 @ X43 ) )
      | ( zip_tseitin_1 @ X45 @ X44 )
      | ( ( k2_relset_1 @ X47 @ X44 @ X46 )
       != X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
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

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('60',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

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
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X41 @ X42 ) ) ),
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
    ! [X39: $i,X40: $i] :
      ( ( v2_funct_1 @ X40 )
      | ~ ( zip_tseitin_0 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('72',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','72'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('74',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('75',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('76',plain,(
    ! [X4: $i] :
      ( ( ( k5_relat_1 @ X4 @ ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('77',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X0 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X0 @ X3 ) ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X2 ) ) @ X1 )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','87'])).

thf('89',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X2 ) ) @ X1 )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X2 ) ) @ X1 )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['82','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['76','93'])).

thf('95',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['74','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('102',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('103',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('104',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X4: $i] :
      ( ( ( k5_relat_1 @ X4 @ ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['107','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['101','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) ) @ X0 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) ) @ X0 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) ) @ sk_D )
      = ( k5_relat_1 @ sk_D @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['73','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_partfun1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('126',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('127',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_relat_1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['7','44'])).

thf('130',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['133','134'])).

thf('136',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('137',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
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

thf('140',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['138','143'])).

thf('145',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('147',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('149',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X49 ) @ X49 )
        = ( k6_relat_1 @ X48 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('151',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['151','152','153','154','155'])).

thf('157',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('163',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('164',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['161','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['148','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['147','169'])).

thf('171',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('172',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_relat_1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('174',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['174','175','176','177','178'])).

thf('180',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('184',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('187',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('191',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('193',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('196',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['184','195'])).

thf('197',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['171','196'])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('199',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('203',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['170','200','203'])).

thf('205',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['35','39','40','41','42','43'])).

thf('206',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('207',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['180','181'])).

thf('208',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['157','158'])).

thf('209',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('210',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['180','181'])).

thf('211',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['210','211'])).

thf('213',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['209','214'])).

thf('216',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('217',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('219',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C )
      = ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['208','218'])).

thf('220',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['187','188'])).

thf('221',plain,(
    ! [X4: $i] :
      ( ( ( k5_relat_1 @ X4 @ ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('222',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('223',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('224',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('226',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['219','224','225'])).

thf('227',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('230',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['207','231'])).

thf('233',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['180','181'])).

thf('234',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['206','234'])).

thf('236',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('237',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['235','236','237'])).

thf('239',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['35','39','40','41','42','43'])).

thf('240',plain,(
    ! [X4: $i] :
      ( ( ( k5_relat_1 @ X4 @ ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('241',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['239','240'])).

thf('242',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['201','202'])).

thf('243',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['201','202'])).

thf('245',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['201','202'])).

thf('247',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('248',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['123','137','204','205','238','243','244','245','246','247'])).

thf('249',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['248','249'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jnDGYrOKhW
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:15:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 35.40/35.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 35.40/35.61  % Solved by: fo/fo7.sh
% 35.40/35.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 35.40/35.61  % done 4698 iterations in 35.131s
% 35.40/35.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 35.40/35.61  % SZS output start Refutation
% 35.40/35.61  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 35.40/35.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 35.40/35.61  thf(sk_A_type, type, sk_A: $i).
% 35.40/35.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 35.40/35.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 35.40/35.61  thf(sk_C_type, type, sk_C: $i).
% 35.40/35.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 35.40/35.61  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 35.40/35.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 35.40/35.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 35.40/35.61  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 35.40/35.61  thf(sk_D_type, type, sk_D: $i).
% 35.40/35.61  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 35.40/35.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 35.40/35.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 35.40/35.61  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 35.40/35.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 35.40/35.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 35.40/35.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 35.40/35.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 35.40/35.61  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 35.40/35.61  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 35.40/35.61  thf(sk_B_type, type, sk_B: $i).
% 35.40/35.61  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 35.40/35.61  thf(t36_funct_2, conjecture,
% 35.40/35.61    (![A:$i,B:$i,C:$i]:
% 35.40/35.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 35.40/35.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 35.40/35.61       ( ![D:$i]:
% 35.40/35.61         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 35.40/35.61             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 35.40/35.61           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 35.40/35.61               ( r2_relset_1 @
% 35.40/35.61                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 35.40/35.61                 ( k6_partfun1 @ A ) ) & 
% 35.40/35.61               ( v2_funct_1 @ C ) ) =>
% 35.40/35.61             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 35.40/35.61               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 35.40/35.61  thf(zf_stmt_0, negated_conjecture,
% 35.40/35.61    (~( ![A:$i,B:$i,C:$i]:
% 35.40/35.61        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 35.40/35.61            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 35.40/35.61          ( ![D:$i]:
% 35.40/35.61            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 35.40/35.61                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 35.40/35.61              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 35.40/35.61                  ( r2_relset_1 @
% 35.40/35.61                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 35.40/35.61                    ( k6_partfun1 @ A ) ) & 
% 35.40/35.61                  ( v2_funct_1 @ C ) ) =>
% 35.40/35.61                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 35.40/35.61                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 35.40/35.61    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 35.40/35.61  thf('0', plain,
% 35.40/35.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf(t35_funct_2, axiom,
% 35.40/35.61    (![A:$i,B:$i,C:$i]:
% 35.40/35.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 35.40/35.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 35.40/35.61       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 35.40/35.61         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 35.40/35.61           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 35.40/35.61             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 35.40/35.61  thf('1', plain,
% 35.40/35.61      (![X48 : $i, X49 : $i, X50 : $i]:
% 35.40/35.61         (((X48) = (k1_xboole_0))
% 35.40/35.61          | ~ (v1_funct_1 @ X49)
% 35.40/35.61          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 35.40/35.61          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 35.40/35.61          | ((k5_relat_1 @ (k2_funct_1 @ X49) @ X49) = (k6_partfun1 @ X48))
% 35.40/35.61          | ~ (v2_funct_1 @ X49)
% 35.40/35.61          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 35.40/35.61      inference('cnf', [status(esa)], [t35_funct_2])).
% 35.40/35.61  thf(redefinition_k6_partfun1, axiom,
% 35.40/35.61    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 35.40/35.61  thf('2', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 35.40/35.61      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 35.40/35.61  thf('3', plain,
% 35.40/35.61      (![X48 : $i, X49 : $i, X50 : $i]:
% 35.40/35.61         (((X48) = (k1_xboole_0))
% 35.40/35.61          | ~ (v1_funct_1 @ X49)
% 35.40/35.61          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 35.40/35.61          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 35.40/35.61          | ((k5_relat_1 @ (k2_funct_1 @ X49) @ X49) = (k6_relat_1 @ X48))
% 35.40/35.61          | ~ (v2_funct_1 @ X49)
% 35.40/35.61          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 35.40/35.61      inference('demod', [status(thm)], ['1', '2'])).
% 35.40/35.61  thf('4', plain,
% 35.40/35.61      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 35.40/35.61        | ~ (v2_funct_1 @ sk_D)
% 35.40/35.61        | ((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_relat_1 @ sk_A))
% 35.40/35.61        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 35.40/35.61        | ~ (v1_funct_1 @ sk_D)
% 35.40/35.61        | ((sk_A) = (k1_xboole_0)))),
% 35.40/35.61      inference('sup-', [status(thm)], ['0', '3'])).
% 35.40/35.61  thf('5', plain,
% 35.40/35.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf(redefinition_k2_relset_1, axiom,
% 35.40/35.61    (![A:$i,B:$i,C:$i]:
% 35.40/35.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 35.40/35.61       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 35.40/35.61  thf('6', plain,
% 35.40/35.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 35.40/35.61         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 35.40/35.61          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 35.40/35.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 35.40/35.61  thf('7', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 35.40/35.61      inference('sup-', [status(thm)], ['5', '6'])).
% 35.40/35.61  thf('8', plain,
% 35.40/35.61      ((r2_relset_1 @ sk_A @ sk_A @ 
% 35.40/35.61        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 35.40/35.61        (k6_partfun1 @ sk_A))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('9', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 35.40/35.61      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 35.40/35.61  thf('10', plain,
% 35.40/35.61      ((r2_relset_1 @ sk_A @ sk_A @ 
% 35.40/35.61        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 35.40/35.61        (k6_relat_1 @ sk_A))),
% 35.40/35.61      inference('demod', [status(thm)], ['8', '9'])).
% 35.40/35.61  thf('11', plain,
% 35.40/35.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('12', plain,
% 35.40/35.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf(dt_k1_partfun1, axiom,
% 35.40/35.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 35.40/35.61     ( ( ( v1_funct_1 @ E ) & 
% 35.40/35.61         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 35.40/35.61         ( v1_funct_1 @ F ) & 
% 35.40/35.61         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 35.40/35.61       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 35.40/35.61         ( m1_subset_1 @
% 35.40/35.61           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 35.40/35.61           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 35.40/35.61  thf('13', plain,
% 35.40/35.61      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 35.40/35.61         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 35.40/35.61          | ~ (v1_funct_1 @ X20)
% 35.40/35.61          | ~ (v1_funct_1 @ X23)
% 35.40/35.61          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 35.40/35.61          | (m1_subset_1 @ (k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23) @ 
% 35.40/35.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X25))))),
% 35.40/35.61      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 35.40/35.61  thf('14', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 35.40/35.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 35.40/35.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 35.40/35.61          | ~ (v1_funct_1 @ X1)
% 35.40/35.61          | ~ (v1_funct_1 @ sk_C))),
% 35.40/35.61      inference('sup-', [status(thm)], ['12', '13'])).
% 35.40/35.61  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('16', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 35.40/35.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 35.40/35.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 35.40/35.61          | ~ (v1_funct_1 @ X1))),
% 35.40/35.61      inference('demod', [status(thm)], ['14', '15'])).
% 35.40/35.61  thf('17', plain,
% 35.40/35.61      ((~ (v1_funct_1 @ sk_D)
% 35.40/35.61        | (m1_subset_1 @ 
% 35.40/35.61           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 35.40/35.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 35.40/35.61      inference('sup-', [status(thm)], ['11', '16'])).
% 35.40/35.61  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('19', plain,
% 35.40/35.61      ((m1_subset_1 @ 
% 35.40/35.61        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 35.40/35.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 35.40/35.61      inference('demod', [status(thm)], ['17', '18'])).
% 35.40/35.61  thf(redefinition_r2_relset_1, axiom,
% 35.40/35.61    (![A:$i,B:$i,C:$i,D:$i]:
% 35.40/35.61     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 35.40/35.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 35.40/35.61       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 35.40/35.61  thf('20', plain,
% 35.40/35.61      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 35.40/35.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 35.40/35.61          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 35.40/35.61          | ((X16) = (X19))
% 35.40/35.61          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 35.40/35.61      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 35.40/35.61  thf('21', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 35.40/35.61             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 35.40/35.61          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 35.40/35.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 35.40/35.61      inference('sup-', [status(thm)], ['19', '20'])).
% 35.40/35.61  thf('22', plain,
% 35.40/35.61      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 35.40/35.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 35.40/35.61        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 35.40/35.61            = (k6_relat_1 @ sk_A)))),
% 35.40/35.61      inference('sup-', [status(thm)], ['10', '21'])).
% 35.40/35.61  thf(dt_k6_partfun1, axiom,
% 35.40/35.61    (![A:$i]:
% 35.40/35.61     ( ( m1_subset_1 @
% 35.40/35.61         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 35.40/35.61       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 35.40/35.61  thf('23', plain,
% 35.40/35.61      (![X27 : $i]:
% 35.40/35.61         (m1_subset_1 @ (k6_partfun1 @ X27) @ 
% 35.40/35.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 35.40/35.61      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 35.40/35.61  thf('24', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 35.40/35.61      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 35.40/35.61  thf('25', plain,
% 35.40/35.61      (![X27 : $i]:
% 35.40/35.61         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 35.40/35.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 35.40/35.61      inference('demod', [status(thm)], ['23', '24'])).
% 35.40/35.61  thf('26', plain,
% 35.40/35.61      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 35.40/35.61         = (k6_relat_1 @ sk_A))),
% 35.40/35.61      inference('demod', [status(thm)], ['22', '25'])).
% 35.40/35.61  thf('27', plain,
% 35.40/35.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf(t24_funct_2, axiom,
% 35.40/35.61    (![A:$i,B:$i,C:$i]:
% 35.40/35.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 35.40/35.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 35.40/35.61       ( ![D:$i]:
% 35.40/35.61         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 35.40/35.61             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 35.40/35.61           ( ( r2_relset_1 @
% 35.40/35.61               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 35.40/35.61               ( k6_partfun1 @ B ) ) =>
% 35.40/35.61             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 35.40/35.61  thf('28', plain,
% 35.40/35.61      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 35.40/35.61         (~ (v1_funct_1 @ X35)
% 35.40/35.61          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 35.40/35.61          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 35.40/35.61          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 35.40/35.61               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 35.40/35.61               (k6_partfun1 @ X36))
% 35.40/35.61          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 35.40/35.61          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 35.40/35.61          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 35.40/35.61          | ~ (v1_funct_1 @ X38))),
% 35.40/35.61      inference('cnf', [status(esa)], [t24_funct_2])).
% 35.40/35.61  thf('29', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 35.40/35.61      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 35.40/35.61  thf('30', plain,
% 35.40/35.61      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 35.40/35.61         (~ (v1_funct_1 @ X35)
% 35.40/35.61          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 35.40/35.61          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 35.40/35.61          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 35.40/35.61               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 35.40/35.61               (k6_relat_1 @ X36))
% 35.40/35.61          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 35.40/35.61          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 35.40/35.61          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 35.40/35.61          | ~ (v1_funct_1 @ X38))),
% 35.40/35.61      inference('demod', [status(thm)], ['28', '29'])).
% 35.40/35.61  thf('31', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 35.40/35.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 35.40/35.61          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 35.40/35.61          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 35.40/35.61               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 35.40/35.61               (k6_relat_1 @ sk_A))
% 35.40/35.61          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 35.40/35.61          | ~ (v1_funct_1 @ sk_C))),
% 35.40/35.61      inference('sup-', [status(thm)], ['27', '30'])).
% 35.40/35.61  thf('32', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('34', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 35.40/35.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 35.40/35.61          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 35.40/35.61          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 35.40/35.61               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 35.40/35.61               (k6_relat_1 @ sk_A)))),
% 35.40/35.61      inference('demod', [status(thm)], ['31', '32', '33'])).
% 35.40/35.61  thf('35', plain,
% 35.40/35.61      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 35.40/35.61           (k6_relat_1 @ sk_A))
% 35.40/35.61        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 35.40/35.61        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 35.40/35.61        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 35.40/35.61        | ~ (v1_funct_1 @ sk_D))),
% 35.40/35.61      inference('sup-', [status(thm)], ['26', '34'])).
% 35.40/35.61  thf('36', plain,
% 35.40/35.61      (![X27 : $i]:
% 35.40/35.61         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 35.40/35.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 35.40/35.61      inference('demod', [status(thm)], ['23', '24'])).
% 35.40/35.61  thf('37', plain,
% 35.40/35.61      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 35.40/35.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 35.40/35.61          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 35.40/35.61          | (r2_relset_1 @ X17 @ X18 @ X16 @ X19)
% 35.40/35.61          | ((X16) != (X19)))),
% 35.40/35.61      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 35.40/35.61  thf('38', plain,
% 35.40/35.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 35.40/35.61         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 35.40/35.61          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 35.40/35.61      inference('simplify', [status(thm)], ['37'])).
% 35.40/35.61  thf('39', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 35.40/35.61      inference('sup-', [status(thm)], ['36', '38'])).
% 35.40/35.61  thf('40', plain,
% 35.40/35.61      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 35.40/35.61      inference('sup-', [status(thm)], ['5', '6'])).
% 35.40/35.61  thf('41', plain,
% 35.40/35.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('42', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('44', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 35.40/35.61      inference('demod', [status(thm)], ['35', '39', '40', '41', '42', '43'])).
% 35.40/35.61  thf('45', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 35.40/35.61      inference('demod', [status(thm)], ['7', '44'])).
% 35.40/35.61  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('48', plain,
% 35.40/35.61      ((((sk_A) != (sk_A))
% 35.40/35.61        | ~ (v2_funct_1 @ sk_D)
% 35.40/35.61        | ((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_relat_1 @ sk_A))
% 35.40/35.61        | ((sk_A) = (k1_xboole_0)))),
% 35.40/35.61      inference('demod', [status(thm)], ['4', '45', '46', '47'])).
% 35.40/35.61  thf('49', plain,
% 35.40/35.61      ((((sk_A) = (k1_xboole_0))
% 35.40/35.61        | ((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_relat_1 @ sk_A))
% 35.40/35.61        | ~ (v2_funct_1 @ sk_D))),
% 35.40/35.61      inference('simplify', [status(thm)], ['48'])).
% 35.40/35.61  thf('50', plain, (((sk_A) != (k1_xboole_0))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('51', plain,
% 35.40/35.61      ((((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_relat_1 @ sk_A))
% 35.40/35.61        | ~ (v2_funct_1 @ sk_D))),
% 35.40/35.61      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 35.40/35.61  thf('52', plain,
% 35.40/35.61      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 35.40/35.61         = (k6_relat_1 @ sk_A))),
% 35.40/35.61      inference('demod', [status(thm)], ['22', '25'])).
% 35.40/35.61  thf('53', plain,
% 35.40/35.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf(t30_funct_2, axiom,
% 35.40/35.61    (![A:$i,B:$i,C:$i,D:$i]:
% 35.40/35.61     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 35.40/35.61         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 35.40/35.61       ( ![E:$i]:
% 35.40/35.61         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 35.40/35.61             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 35.40/35.61           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 35.40/35.61               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 35.40/35.61             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 35.40/35.61               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 35.40/35.61  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 35.40/35.61  thf(zf_stmt_2, axiom,
% 35.40/35.61    (![C:$i,B:$i]:
% 35.40/35.61     ( ( zip_tseitin_1 @ C @ B ) =>
% 35.40/35.61       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 35.40/35.61  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 35.40/35.61  thf(zf_stmt_4, axiom,
% 35.40/35.61    (![E:$i,D:$i]:
% 35.40/35.61     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 35.40/35.61  thf(zf_stmt_5, axiom,
% 35.40/35.61    (![A:$i,B:$i,C:$i,D:$i]:
% 35.40/35.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 35.40/35.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 35.40/35.61       ( ![E:$i]:
% 35.40/35.61         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 35.40/35.61             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 35.40/35.61           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 35.40/35.61               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 35.40/35.61             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 35.40/35.61  thf('54', plain,
% 35.40/35.61      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 35.40/35.61         (~ (v1_funct_1 @ X43)
% 35.40/35.61          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 35.40/35.61          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 35.40/35.61          | (zip_tseitin_0 @ X43 @ X46)
% 35.40/35.61          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X44 @ X44 @ X45 @ X46 @ X43))
% 35.40/35.61          | (zip_tseitin_1 @ X45 @ X44)
% 35.40/35.61          | ((k2_relset_1 @ X47 @ X44 @ X46) != (X44))
% 35.40/35.61          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X44)))
% 35.40/35.61          | ~ (v1_funct_2 @ X46 @ X47 @ X44)
% 35.40/35.61          | ~ (v1_funct_1 @ X46))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 35.40/35.61  thf('55', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 35.40/35.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 35.40/35.61          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 35.40/35.61          | (zip_tseitin_1 @ sk_A @ sk_B)
% 35.40/35.61          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 35.40/35.61          | (zip_tseitin_0 @ sk_D @ X0)
% 35.40/35.61          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 35.40/35.61          | ~ (v1_funct_1 @ sk_D))),
% 35.40/35.61      inference('sup-', [status(thm)], ['53', '54'])).
% 35.40/35.61  thf('56', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('58', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 35.40/35.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 35.40/35.61          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 35.40/35.61          | (zip_tseitin_1 @ sk_A @ sk_B)
% 35.40/35.61          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 35.40/35.61          | (zip_tseitin_0 @ sk_D @ X0))),
% 35.40/35.61      inference('demod', [status(thm)], ['55', '56', '57'])).
% 35.40/35.61  thf('59', plain,
% 35.40/35.61      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 35.40/35.61        | (zip_tseitin_0 @ sk_D @ sk_C)
% 35.40/35.61        | (zip_tseitin_1 @ sk_A @ sk_B)
% 35.40/35.61        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 35.40/35.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 35.40/35.61        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 35.40/35.61        | ~ (v1_funct_1 @ sk_C))),
% 35.40/35.61      inference('sup-', [status(thm)], ['52', '58'])).
% 35.40/35.61  thf(fc4_funct_1, axiom,
% 35.40/35.61    (![A:$i]:
% 35.40/35.61     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 35.40/35.61       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 35.40/35.61  thf('60', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 35.40/35.61      inference('cnf', [status(esa)], [fc4_funct_1])).
% 35.40/35.61  thf('61', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('62', plain,
% 35.40/35.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('63', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('65', plain,
% 35.40/35.61      (((zip_tseitin_0 @ sk_D @ sk_C)
% 35.40/35.61        | (zip_tseitin_1 @ sk_A @ sk_B)
% 35.40/35.61        | ((sk_B) != (sk_B)))),
% 35.40/35.61      inference('demod', [status(thm)], ['59', '60', '61', '62', '63', '64'])).
% 35.40/35.61  thf('66', plain,
% 35.40/35.61      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 35.40/35.61      inference('simplify', [status(thm)], ['65'])).
% 35.40/35.61  thf('67', plain,
% 35.40/35.61      (![X41 : $i, X42 : $i]:
% 35.40/35.61         (((X41) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X41 @ X42))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 35.40/35.61  thf('68', plain,
% 35.40/35.61      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 35.40/35.61      inference('sup-', [status(thm)], ['66', '67'])).
% 35.40/35.61  thf('69', plain, (((sk_A) != (k1_xboole_0))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('70', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 35.40/35.61      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 35.40/35.61  thf('71', plain,
% 35.40/35.61      (![X39 : $i, X40 : $i]:
% 35.40/35.61         ((v2_funct_1 @ X40) | ~ (zip_tseitin_0 @ X40 @ X39))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_4])).
% 35.40/35.61  thf('72', plain, ((v2_funct_1 @ sk_D)),
% 35.40/35.61      inference('sup-', [status(thm)], ['70', '71'])).
% 35.40/35.61  thf('73', plain,
% 35.40/35.61      (((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_relat_1 @ sk_A))),
% 35.40/35.61      inference('demod', [status(thm)], ['51', '72'])).
% 35.40/35.61  thf(dt_k2_funct_1, axiom,
% 35.40/35.61    (![A:$i]:
% 35.40/35.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 35.40/35.61       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 35.40/35.61         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 35.40/35.61  thf('74', plain,
% 35.40/35.61      (![X5 : $i]:
% 35.40/35.61         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 35.40/35.61          | ~ (v1_funct_1 @ X5)
% 35.40/35.61          | ~ (v1_relat_1 @ X5))),
% 35.40/35.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 35.40/35.61  thf(t55_funct_1, axiom,
% 35.40/35.61    (![A:$i]:
% 35.40/35.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 35.40/35.61       ( ( v2_funct_1 @ A ) =>
% 35.40/35.61         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 35.40/35.61           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 35.40/35.61  thf('75', plain,
% 35.40/35.61      (![X8 : $i]:
% 35.40/35.61         (~ (v2_funct_1 @ X8)
% 35.40/35.61          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 35.40/35.61          | ~ (v1_funct_1 @ X8)
% 35.40/35.61          | ~ (v1_relat_1 @ X8))),
% 35.40/35.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 35.40/35.61  thf(t80_relat_1, axiom,
% 35.40/35.61    (![A:$i]:
% 35.40/35.61     ( ( v1_relat_1 @ A ) =>
% 35.40/35.61       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 35.40/35.61  thf('76', plain,
% 35.40/35.61      (![X4 : $i]:
% 35.40/35.61         (((k5_relat_1 @ X4 @ (k6_relat_1 @ (k2_relat_1 @ X4))) = (X4))
% 35.40/35.61          | ~ (v1_relat_1 @ X4))),
% 35.40/35.61      inference('cnf', [status(esa)], [t80_relat_1])).
% 35.40/35.61  thf(t78_relat_1, axiom,
% 35.40/35.61    (![A:$i]:
% 35.40/35.61     ( ( v1_relat_1 @ A ) =>
% 35.40/35.61       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 35.40/35.61  thf('77', plain,
% 35.40/35.61      (![X3 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X3)) @ X3) = (X3))
% 35.40/35.61          | ~ (v1_relat_1 @ X3))),
% 35.40/35.61      inference('cnf', [status(esa)], [t78_relat_1])).
% 35.40/35.61  thf(t55_relat_1, axiom,
% 35.40/35.61    (![A:$i]:
% 35.40/35.61     ( ( v1_relat_1 @ A ) =>
% 35.40/35.61       ( ![B:$i]:
% 35.40/35.61         ( ( v1_relat_1 @ B ) =>
% 35.40/35.61           ( ![C:$i]:
% 35.40/35.61             ( ( v1_relat_1 @ C ) =>
% 35.40/35.61               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 35.40/35.61                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 35.40/35.61  thf('78', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 35.40/35.61              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 35.40/35.61          | ~ (v1_relat_1 @ X2)
% 35.40/35.61          | ~ (v1_relat_1 @ X1))),
% 35.40/35.61      inference('cnf', [status(esa)], [t55_relat_1])).
% 35.40/35.61  thf('79', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (((k5_relat_1 @ X0 @ X1)
% 35.40/35.61            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 35.40/35.61               (k5_relat_1 @ X0 @ X1)))
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X0))),
% 35.40/35.61      inference('sup+', [status(thm)], ['77', '78'])).
% 35.40/35.61  thf('80', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 35.40/35.61      inference('cnf', [status(esa)], [fc4_funct_1])).
% 35.40/35.61  thf('81', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (((k5_relat_1 @ X0 @ X1)
% 35.40/35.61            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 35.40/35.61               (k5_relat_1 @ X0 @ X1)))
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X0))),
% 35.40/35.61      inference('demod', [status(thm)], ['79', '80'])).
% 35.40/35.61  thf('82', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ X0 @ X1)
% 35.40/35.61              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 35.40/35.61                 (k5_relat_1 @ X0 @ X1))))),
% 35.40/35.61      inference('simplify', [status(thm)], ['81'])).
% 35.40/35.61  thf('83', plain,
% 35.40/35.61      (![X3 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X3)) @ X3) = (X3))
% 35.40/35.61          | ~ (v1_relat_1 @ X3))),
% 35.40/35.61      inference('cnf', [status(esa)], [t78_relat_1])).
% 35.40/35.61  thf('84', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 35.40/35.61              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 35.40/35.61          | ~ (v1_relat_1 @ X2)
% 35.40/35.61          | ~ (v1_relat_1 @ X1))),
% 35.40/35.61      inference('cnf', [status(esa)], [t55_relat_1])).
% 35.40/35.61  thf('85', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 35.40/35.61              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 35.40/35.61          | ~ (v1_relat_1 @ X2)
% 35.40/35.61          | ~ (v1_relat_1 @ X1))),
% 35.40/35.61      inference('cnf', [status(esa)], [t55_relat_1])).
% 35.40/35.61  thf('86', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X3)
% 35.40/35.61            = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k5_relat_1 @ X0 @ X3)))
% 35.40/35.61          | ~ (v1_relat_1 @ X2)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 35.40/35.61          | ~ (v1_relat_1 @ X3)
% 35.40/35.61          | ~ (v1_relat_1 @ X0))),
% 35.40/35.61      inference('sup+', [status(thm)], ['84', '85'])).
% 35.40/35.61  thf('87', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X3)
% 35.40/35.61          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X2)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X3)
% 35.40/35.61              = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k5_relat_1 @ X0 @ X3))))),
% 35.40/35.61      inference('simplify', [status(thm)], ['86'])).
% 35.40/35.61  thf('88', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ 
% 35.40/35.61              (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 35.40/35.61               (k5_relat_1 @ X0 @ X2)) @ 
% 35.40/35.61              X1)
% 35.40/35.61              = (k5_relat_1 @ 
% 35.40/35.61                 (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) @ 
% 35.40/35.61                 (k5_relat_1 @ X2 @ X1)))
% 35.40/35.61          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 35.40/35.61          | ~ (v1_relat_1 @ X2)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X1))),
% 35.40/35.61      inference('sup-', [status(thm)], ['83', '87'])).
% 35.40/35.61  thf('89', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 35.40/35.61      inference('cnf', [status(esa)], [fc4_funct_1])).
% 35.40/35.61  thf('90', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ 
% 35.40/35.61              (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 35.40/35.61               (k5_relat_1 @ X0 @ X2)) @ 
% 35.40/35.61              X1)
% 35.40/35.61              = (k5_relat_1 @ 
% 35.40/35.61                 (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) @ 
% 35.40/35.61                 (k5_relat_1 @ X2 @ X1)))
% 35.40/35.61          | ~ (v1_relat_1 @ X2)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X1))),
% 35.40/35.61      inference('demod', [status(thm)], ['88', '89'])).
% 35.40/35.61  thf('91', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X2)
% 35.40/35.61          | ((k5_relat_1 @ 
% 35.40/35.61              (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 35.40/35.61               (k5_relat_1 @ X0 @ X2)) @ 
% 35.40/35.61              X1)
% 35.40/35.61              = (k5_relat_1 @ 
% 35.40/35.61                 (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) @ 
% 35.40/35.61                 (k5_relat_1 @ X2 @ X1)))
% 35.40/35.61          | ~ (v1_relat_1 @ X0))),
% 35.40/35.61      inference('simplify', [status(thm)], ['90'])).
% 35.40/35.61  thf('92', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 35.40/35.61            = (k5_relat_1 @ 
% 35.40/35.61               (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ X1) @ 
% 35.40/35.61               (k5_relat_1 @ X0 @ X2)))
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X2))),
% 35.40/35.61      inference('sup+', [status(thm)], ['82', '91'])).
% 35.40/35.61  thf('93', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X2)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 35.40/35.61              = (k5_relat_1 @ 
% 35.40/35.61                 (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ X1) @ 
% 35.40/35.61                 (k5_relat_1 @ X0 @ X2))))),
% 35.40/35.61      inference('simplify', [status(thm)], ['92'])).
% 35.40/35.61  thf('94', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 35.40/35.61            (k6_relat_1 @ (k2_relat_1 @ X0)))
% 35.40/35.61            = (k5_relat_1 @ 
% 35.40/35.61               (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ X1) @ X0))
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 35.40/35.61      inference('sup+', [status(thm)], ['76', '93'])).
% 35.40/35.61  thf('95', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 35.40/35.61      inference('cnf', [status(esa)], [fc4_funct_1])).
% 35.40/35.61  thf('96', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 35.40/35.61            (k6_relat_1 @ (k2_relat_1 @ X0)))
% 35.40/35.61            = (k5_relat_1 @ 
% 35.40/35.61               (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ X1) @ X0))
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X0))),
% 35.40/35.61      inference('demod', [status(thm)], ['94', '95'])).
% 35.40/35.61  thf('97', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 35.40/35.61              (k6_relat_1 @ (k2_relat_1 @ X0)))
% 35.40/35.61              = (k5_relat_1 @ 
% 35.40/35.61                 (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ X1) @ X0)))),
% 35.40/35.61      inference('simplify', [status(thm)], ['96'])).
% 35.40/35.61  thf('98', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 35.40/35.61            (k6_relat_1 @ (k2_relat_1 @ X1)))
% 35.40/35.61            = (k5_relat_1 @ 
% 35.40/35.61               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 35.40/35.61                (k2_funct_1 @ X0)) @ 
% 35.40/35.61               X1))
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v2_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 35.40/35.61      inference('sup+', [status(thm)], ['75', '97'])).
% 35.40/35.61  thf('99', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v2_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 35.40/35.61              (k6_relat_1 @ (k2_relat_1 @ X1)))
% 35.40/35.61              = (k5_relat_1 @ 
% 35.40/35.61                 (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 35.40/35.61                  (k2_funct_1 @ X0)) @ 
% 35.40/35.61                 X1)))),
% 35.40/35.61      inference('sup-', [status(thm)], ['74', '98'])).
% 35.40/35.61  thf('100', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 35.40/35.61            (k6_relat_1 @ (k2_relat_1 @ X1)))
% 35.40/35.61            = (k5_relat_1 @ 
% 35.40/35.61               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 35.40/35.61                (k2_funct_1 @ X0)) @ 
% 35.40/35.61               X1))
% 35.40/35.61          | ~ (v2_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X0))),
% 35.40/35.61      inference('simplify', [status(thm)], ['99'])).
% 35.40/35.61  thf('101', plain,
% 35.40/35.61      (![X5 : $i]:
% 35.40/35.61         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 35.40/35.61          | ~ (v1_funct_1 @ X5)
% 35.40/35.61          | ~ (v1_relat_1 @ X5))),
% 35.40/35.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 35.40/35.61  thf('102', plain,
% 35.40/35.61      (![X5 : $i]:
% 35.40/35.61         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 35.40/35.61          | ~ (v1_funct_1 @ X5)
% 35.40/35.61          | ~ (v1_relat_1 @ X5))),
% 35.40/35.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 35.40/35.61  thf('103', plain,
% 35.40/35.61      (![X8 : $i]:
% 35.40/35.61         (~ (v2_funct_1 @ X8)
% 35.40/35.61          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 35.40/35.61          | ~ (v1_funct_1 @ X8)
% 35.40/35.61          | ~ (v1_relat_1 @ X8))),
% 35.40/35.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 35.40/35.61  thf('104', plain,
% 35.40/35.61      (![X3 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X3)) @ X3) = (X3))
% 35.40/35.61          | ~ (v1_relat_1 @ X3))),
% 35.40/35.61      inference('cnf', [status(esa)], [t78_relat_1])).
% 35.40/35.61  thf('105', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 35.40/35.61            = (k2_funct_1 @ X0))
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v2_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 35.40/35.61      inference('sup+', [status(thm)], ['103', '104'])).
% 35.40/35.61  thf('106', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v2_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 35.40/35.61              = (k2_funct_1 @ X0)))),
% 35.40/35.61      inference('sup-', [status(thm)], ['102', '105'])).
% 35.40/35.61  thf('107', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 35.40/35.61            = (k2_funct_1 @ X0))
% 35.40/35.61          | ~ (v2_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X0))),
% 35.40/35.61      inference('simplify', [status(thm)], ['106'])).
% 35.40/35.61  thf('108', plain,
% 35.40/35.61      (![X4 : $i]:
% 35.40/35.61         (((k5_relat_1 @ X4 @ (k6_relat_1 @ (k2_relat_1 @ X4))) = (X4))
% 35.40/35.61          | ~ (v1_relat_1 @ X4))),
% 35.40/35.61      inference('cnf', [status(esa)], [t80_relat_1])).
% 35.40/35.61  thf('109', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 35.40/35.61              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 35.40/35.61          | ~ (v1_relat_1 @ X2)
% 35.40/35.61          | ~ (v1_relat_1 @ X1))),
% 35.40/35.61      inference('cnf', [status(esa)], [t55_relat_1])).
% 35.40/35.61  thf('110', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (((k5_relat_1 @ X0 @ X1)
% 35.40/35.61            = (k5_relat_1 @ X0 @ 
% 35.40/35.61               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 35.40/35.61      inference('sup+', [status(thm)], ['108', '109'])).
% 35.40/35.61  thf('111', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 35.40/35.61      inference('cnf', [status(esa)], [fc4_funct_1])).
% 35.40/35.61  thf('112', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (((k5_relat_1 @ X0 @ X1)
% 35.40/35.61            = (k5_relat_1 @ X0 @ 
% 35.40/35.61               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X1))),
% 35.40/35.61      inference('demod', [status(thm)], ['110', '111'])).
% 35.40/35.61  thf('113', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ X0 @ X1)
% 35.40/35.61              = (k5_relat_1 @ X0 @ 
% 35.40/35.61                 (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1))))),
% 35.40/35.61      inference('simplify', [status(thm)], ['112'])).
% 35.40/35.61  thf('114', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 35.40/35.61              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 35.40/35.61          | ~ (v1_relat_1 @ X2)
% 35.40/35.61          | ~ (v1_relat_1 @ X1))),
% 35.40/35.61      inference('cnf', [status(esa)], [t55_relat_1])).
% 35.40/35.61  thf('115', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 35.40/35.61            = (k5_relat_1 @ X1 @ 
% 35.40/35.61               (k5_relat_1 @ 
% 35.40/35.61                (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X1)) @ X0) @ X2)))
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X2)
% 35.40/35.61          | ~ (v1_relat_1 @ 
% 35.40/35.61               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X1)) @ X0)))),
% 35.40/35.61      inference('sup+', [status(thm)], ['113', '114'])).
% 35.40/35.61  thf('116', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X1)) @ X0))
% 35.40/35.61          | ~ (v1_relat_1 @ X2)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 35.40/35.61              = (k5_relat_1 @ X1 @ 
% 35.40/35.61                 (k5_relat_1 @ 
% 35.40/35.61                  (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X1)) @ X0) @ X2))))),
% 35.40/35.61      inference('simplify', [status(thm)], ['115'])).
% 35.40/35.61  thf('117', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v2_funct_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 35.40/35.61              = (k5_relat_1 @ X0 @ 
% 35.40/35.61                 (k5_relat_1 @ 
% 35.40/35.61                  (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 35.40/35.61                   (k2_funct_1 @ X0)) @ 
% 35.40/35.61                  X1)))
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 35.40/35.61          | ~ (v1_relat_1 @ X1))),
% 35.40/35.61      inference('sup-', [status(thm)], ['107', '116'])).
% 35.40/35.61  thf('118', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X1)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 35.40/35.61              = (k5_relat_1 @ X0 @ 
% 35.40/35.61                 (k5_relat_1 @ 
% 35.40/35.61                  (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 35.40/35.61                   (k2_funct_1 @ X0)) @ 
% 35.40/35.61                  X1)))
% 35.40/35.61          | ~ (v2_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 35.40/35.61      inference('simplify', [status(thm)], ['117'])).
% 35.40/35.61  thf('119', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v2_funct_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 35.40/35.61              = (k5_relat_1 @ X0 @ 
% 35.40/35.61                 (k5_relat_1 @ 
% 35.40/35.61                  (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 35.40/35.61                   (k2_funct_1 @ X0)) @ 
% 35.40/35.61                  X1)))
% 35.40/35.61          | ~ (v1_relat_1 @ X1))),
% 35.40/35.61      inference('sup-', [status(thm)], ['101', '118'])).
% 35.40/35.61  thf('120', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X1)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 35.40/35.61              = (k5_relat_1 @ X0 @ 
% 35.40/35.61                 (k5_relat_1 @ 
% 35.40/35.61                  (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 35.40/35.61                   (k2_funct_1 @ X0)) @ 
% 35.40/35.61                  X1)))
% 35.40/35.61          | ~ (v2_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X0))),
% 35.40/35.61      inference('simplify', [status(thm)], ['119'])).
% 35.40/35.61  thf('121', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X1)) @ X0)
% 35.40/35.61            = (k5_relat_1 @ X1 @ 
% 35.40/35.61               (k5_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X1) @ X0) @ 
% 35.40/35.61                (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_funct_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v2_funct_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ~ (v1_funct_1 @ X1)
% 35.40/35.61          | ~ (v2_funct_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X0))),
% 35.40/35.61      inference('sup+', [status(thm)], ['100', '120'])).
% 35.40/35.61  thf('122', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i]:
% 35.40/35.61         (~ (v2_funct_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_1 @ X1)
% 35.40/35.61          | ~ (v1_relat_1 @ X1)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X1)) @ X0)
% 35.40/35.61              = (k5_relat_1 @ X1 @ 
% 35.40/35.61                 (k5_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X1) @ X0) @ 
% 35.40/35.61                  (k6_relat_1 @ (k2_relat_1 @ X0))))))),
% 35.40/35.61      inference('simplify', [status(thm)], ['121'])).
% 35.40/35.61  thf('123', plain,
% 35.40/35.61      ((((k5_relat_1 @ (k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) @ sk_D)
% 35.40/35.61          = (k5_relat_1 @ sk_D @ 
% 35.40/35.61             (k5_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 35.40/35.61              (k6_relat_1 @ (k2_relat_1 @ sk_D)))))
% 35.40/35.61        | ~ (v1_relat_1 @ sk_D)
% 35.40/35.61        | ~ (v1_funct_1 @ sk_D)
% 35.40/35.61        | ~ (v1_relat_1 @ sk_D)
% 35.40/35.61        | ~ (v2_funct_1 @ sk_D))),
% 35.40/35.61      inference('sup+', [status(thm)], ['73', '122'])).
% 35.40/35.61  thf('124', plain,
% 35.40/35.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('125', plain,
% 35.40/35.61      (![X48 : $i, X49 : $i, X50 : $i]:
% 35.40/35.61         (((X48) = (k1_xboole_0))
% 35.40/35.61          | ~ (v1_funct_1 @ X49)
% 35.40/35.61          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 35.40/35.61          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 35.40/35.61          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_partfun1 @ X50))
% 35.40/35.61          | ~ (v2_funct_1 @ X49)
% 35.40/35.61          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 35.40/35.61      inference('cnf', [status(esa)], [t35_funct_2])).
% 35.40/35.61  thf('126', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 35.40/35.61      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 35.40/35.61  thf('127', plain,
% 35.40/35.61      (![X48 : $i, X49 : $i, X50 : $i]:
% 35.40/35.61         (((X48) = (k1_xboole_0))
% 35.40/35.61          | ~ (v1_funct_1 @ X49)
% 35.40/35.61          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 35.40/35.61          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 35.40/35.61          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_relat_1 @ X50))
% 35.40/35.61          | ~ (v2_funct_1 @ X49)
% 35.40/35.61          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 35.40/35.61      inference('demod', [status(thm)], ['125', '126'])).
% 35.40/35.61  thf('128', plain,
% 35.40/35.61      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 35.40/35.61        | ~ (v2_funct_1 @ sk_D)
% 35.40/35.61        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 35.40/35.61        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 35.40/35.61        | ~ (v1_funct_1 @ sk_D)
% 35.40/35.61        | ((sk_A) = (k1_xboole_0)))),
% 35.40/35.61      inference('sup-', [status(thm)], ['124', '127'])).
% 35.40/35.61  thf('129', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 35.40/35.61      inference('demod', [status(thm)], ['7', '44'])).
% 35.40/35.61  thf('130', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('131', plain, ((v1_funct_1 @ sk_D)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('132', plain,
% 35.40/35.61      ((((sk_A) != (sk_A))
% 35.40/35.61        | ~ (v2_funct_1 @ sk_D)
% 35.40/35.61        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 35.40/35.61        | ((sk_A) = (k1_xboole_0)))),
% 35.40/35.61      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 35.40/35.61  thf('133', plain,
% 35.40/35.61      ((((sk_A) = (k1_xboole_0))
% 35.40/35.61        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 35.40/35.61        | ~ (v2_funct_1 @ sk_D))),
% 35.40/35.61      inference('simplify', [status(thm)], ['132'])).
% 35.40/35.61  thf('134', plain, (((sk_A) != (k1_xboole_0))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('135', plain,
% 35.40/35.61      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 35.40/35.61        | ~ (v2_funct_1 @ sk_D))),
% 35.40/35.61      inference('simplify_reflect-', [status(thm)], ['133', '134'])).
% 35.40/35.61  thf('136', plain, ((v2_funct_1 @ sk_D)),
% 35.40/35.61      inference('sup-', [status(thm)], ['70', '71'])).
% 35.40/35.61  thf('137', plain,
% 35.40/35.61      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 35.40/35.61      inference('demod', [status(thm)], ['135', '136'])).
% 35.40/35.61  thf('138', plain,
% 35.40/35.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('139', plain,
% 35.40/35.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf(redefinition_k1_partfun1, axiom,
% 35.40/35.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 35.40/35.61     ( ( ( v1_funct_1 @ E ) & 
% 35.40/35.61         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 35.40/35.61         ( v1_funct_1 @ F ) & 
% 35.40/35.61         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 35.40/35.61       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 35.40/35.61  thf('140', plain,
% 35.40/35.61      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 35.40/35.61         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 35.40/35.61          | ~ (v1_funct_1 @ X28)
% 35.40/35.61          | ~ (v1_funct_1 @ X31)
% 35.40/35.61          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 35.40/35.61          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 35.40/35.61              = (k5_relat_1 @ X28 @ X31)))),
% 35.40/35.61      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 35.40/35.61  thf('141', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 35.40/35.61            = (k5_relat_1 @ sk_C @ X0))
% 35.40/35.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 35.40/35.61          | ~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_1 @ sk_C))),
% 35.40/35.61      inference('sup-', [status(thm)], ['139', '140'])).
% 35.40/35.61  thf('142', plain, ((v1_funct_1 @ sk_C)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('143', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 35.40/35.61            = (k5_relat_1 @ sk_C @ X0))
% 35.40/35.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 35.40/35.61          | ~ (v1_funct_1 @ X0))),
% 35.40/35.61      inference('demod', [status(thm)], ['141', '142'])).
% 35.40/35.61  thf('144', plain,
% 35.40/35.61      ((~ (v1_funct_1 @ sk_D)
% 35.40/35.61        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 35.40/35.61            = (k5_relat_1 @ sk_C @ sk_D)))),
% 35.40/35.61      inference('sup-', [status(thm)], ['138', '143'])).
% 35.40/35.61  thf('145', plain, ((v1_funct_1 @ sk_D)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('146', plain,
% 35.40/35.61      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 35.40/35.61         = (k6_relat_1 @ sk_A))),
% 35.40/35.61      inference('demod', [status(thm)], ['22', '25'])).
% 35.40/35.61  thf('147', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 35.40/35.61      inference('demod', [status(thm)], ['144', '145', '146'])).
% 35.40/35.61  thf('148', plain,
% 35.40/35.61      (![X5 : $i]:
% 35.40/35.61         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 35.40/35.61          | ~ (v1_funct_1 @ X5)
% 35.40/35.61          | ~ (v1_relat_1 @ X5))),
% 35.40/35.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 35.40/35.61  thf('149', plain,
% 35.40/35.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('150', plain,
% 35.40/35.61      (![X48 : $i, X49 : $i, X50 : $i]:
% 35.40/35.61         (((X48) = (k1_xboole_0))
% 35.40/35.61          | ~ (v1_funct_1 @ X49)
% 35.40/35.61          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 35.40/35.61          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 35.40/35.61          | ((k5_relat_1 @ (k2_funct_1 @ X49) @ X49) = (k6_relat_1 @ X48))
% 35.40/35.61          | ~ (v2_funct_1 @ X49)
% 35.40/35.61          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 35.40/35.61      inference('demod', [status(thm)], ['1', '2'])).
% 35.40/35.61  thf('151', plain,
% 35.40/35.61      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 35.40/35.61        | ~ (v2_funct_1 @ sk_C)
% 35.40/35.61        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 35.40/35.61        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 35.40/35.61        | ~ (v1_funct_1 @ sk_C)
% 35.40/35.61        | ((sk_B) = (k1_xboole_0)))),
% 35.40/35.61      inference('sup-', [status(thm)], ['149', '150'])).
% 35.40/35.61  thf('152', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('153', plain, ((v2_funct_1 @ sk_C)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('154', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('155', plain, ((v1_funct_1 @ sk_C)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('156', plain,
% 35.40/35.61      ((((sk_B) != (sk_B))
% 35.40/35.61        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 35.40/35.61        | ((sk_B) = (k1_xboole_0)))),
% 35.40/35.61      inference('demod', [status(thm)], ['151', '152', '153', '154', '155'])).
% 35.40/35.61  thf('157', plain,
% 35.40/35.61      ((((sk_B) = (k1_xboole_0))
% 35.40/35.61        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 35.40/35.61      inference('simplify', [status(thm)], ['156'])).
% 35.40/35.61  thf('158', plain, (((sk_B) != (k1_xboole_0))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('159', plain,
% 35.40/35.61      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 35.40/35.61      inference('simplify_reflect-', [status(thm)], ['157', '158'])).
% 35.40/35.61  thf('160', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 35.40/35.61              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 35.40/35.61          | ~ (v1_relat_1 @ X2)
% 35.40/35.61          | ~ (v1_relat_1 @ X1))),
% 35.40/35.61      inference('cnf', [status(esa)], [t55_relat_1])).
% 35.40/35.61  thf('161', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 35.40/35.61            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 35.40/35.61          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ sk_C))),
% 35.40/35.61      inference('sup+', [status(thm)], ['159', '160'])).
% 35.40/35.61  thf('162', plain,
% 35.40/35.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf(cc1_relset_1, axiom,
% 35.40/35.61    (![A:$i,B:$i,C:$i]:
% 35.40/35.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 35.40/35.61       ( v1_relat_1 @ C ) ))).
% 35.40/35.61  thf('163', plain,
% 35.40/35.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 35.40/35.61         ((v1_relat_1 @ X10)
% 35.40/35.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 35.40/35.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 35.40/35.61  thf('164', plain, ((v1_relat_1 @ sk_C)),
% 35.40/35.61      inference('sup-', [status(thm)], ['162', '163'])).
% 35.40/35.61  thf('165', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 35.40/35.61            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 35.40/35.61          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 35.40/35.61          | ~ (v1_relat_1 @ X0))),
% 35.40/35.61      inference('demod', [status(thm)], ['161', '164'])).
% 35.40/35.61  thf('166', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ sk_C)
% 35.40/35.61          | ~ (v1_funct_1 @ sk_C)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 35.40/35.61              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 35.40/35.61      inference('sup-', [status(thm)], ['148', '165'])).
% 35.40/35.61  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 35.40/35.61      inference('sup-', [status(thm)], ['162', '163'])).
% 35.40/35.61  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('169', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 35.40/35.61              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 35.40/35.61      inference('demod', [status(thm)], ['166', '167', '168'])).
% 35.40/35.61  thf('170', plain,
% 35.40/35.61      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D)
% 35.40/35.61          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 35.40/35.61        | ~ (v1_relat_1 @ sk_D))),
% 35.40/35.61      inference('sup+', [status(thm)], ['147', '169'])).
% 35.40/35.61  thf('171', plain,
% 35.40/35.61      (![X5 : $i]:
% 35.40/35.61         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 35.40/35.61          | ~ (v1_funct_1 @ X5)
% 35.40/35.61          | ~ (v1_relat_1 @ X5))),
% 35.40/35.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 35.40/35.61  thf('172', plain,
% 35.40/35.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('173', plain,
% 35.40/35.61      (![X48 : $i, X49 : $i, X50 : $i]:
% 35.40/35.61         (((X48) = (k1_xboole_0))
% 35.40/35.61          | ~ (v1_funct_1 @ X49)
% 35.40/35.61          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 35.40/35.61          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 35.40/35.61          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_relat_1 @ X50))
% 35.40/35.61          | ~ (v2_funct_1 @ X49)
% 35.40/35.61          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 35.40/35.61      inference('demod', [status(thm)], ['125', '126'])).
% 35.40/35.61  thf('174', plain,
% 35.40/35.61      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 35.40/35.61        | ~ (v2_funct_1 @ sk_C)
% 35.40/35.61        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 35.40/35.61        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 35.40/35.61        | ~ (v1_funct_1 @ sk_C)
% 35.40/35.61        | ((sk_B) = (k1_xboole_0)))),
% 35.40/35.61      inference('sup-', [status(thm)], ['172', '173'])).
% 35.40/35.61  thf('175', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('176', plain, ((v2_funct_1 @ sk_C)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('177', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('178', plain, ((v1_funct_1 @ sk_C)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('179', plain,
% 35.40/35.61      ((((sk_B) != (sk_B))
% 35.40/35.61        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 35.40/35.61        | ((sk_B) = (k1_xboole_0)))),
% 35.40/35.61      inference('demod', [status(thm)], ['174', '175', '176', '177', '178'])).
% 35.40/35.61  thf('180', plain,
% 35.40/35.61      ((((sk_B) = (k1_xboole_0))
% 35.40/35.61        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 35.40/35.61      inference('simplify', [status(thm)], ['179'])).
% 35.40/35.61  thf('181', plain, (((sk_B) != (k1_xboole_0))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('182', plain,
% 35.40/35.61      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 35.40/35.61      inference('simplify_reflect-', [status(thm)], ['180', '181'])).
% 35.40/35.61  thf('183', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 35.40/35.61              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 35.40/35.61      inference('demod', [status(thm)], ['166', '167', '168'])).
% 35.40/35.61  thf('184', plain,
% 35.40/35.61      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 35.40/35.61          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 35.40/35.61        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 35.40/35.61      inference('sup+', [status(thm)], ['182', '183'])).
% 35.40/35.61  thf('185', plain,
% 35.40/35.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('186', plain,
% 35.40/35.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 35.40/35.61         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 35.40/35.61          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 35.40/35.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 35.40/35.61  thf('187', plain,
% 35.40/35.61      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 35.40/35.61      inference('sup-', [status(thm)], ['185', '186'])).
% 35.40/35.61  thf('188', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('189', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 35.40/35.61      inference('sup+', [status(thm)], ['187', '188'])).
% 35.40/35.61  thf('190', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 35.40/35.61            = (k2_funct_1 @ X0))
% 35.40/35.61          | ~ (v2_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_funct_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ X0))),
% 35.40/35.61      inference('simplify', [status(thm)], ['106'])).
% 35.40/35.61  thf('191', plain,
% 35.40/35.61      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 35.40/35.61          = (k2_funct_1 @ sk_C))
% 35.40/35.61        | ~ (v1_relat_1 @ sk_C)
% 35.40/35.61        | ~ (v1_funct_1 @ sk_C)
% 35.40/35.61        | ~ (v2_funct_1 @ sk_C))),
% 35.40/35.61      inference('sup+', [status(thm)], ['189', '190'])).
% 35.40/35.61  thf('192', plain, ((v1_relat_1 @ sk_C)),
% 35.40/35.61      inference('sup-', [status(thm)], ['162', '163'])).
% 35.40/35.61  thf('193', plain, ((v1_funct_1 @ sk_C)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('194', plain, ((v2_funct_1 @ sk_C)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('195', plain,
% 35.40/35.61      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 35.40/35.61         = (k2_funct_1 @ sk_C))),
% 35.40/35.61      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 35.40/35.61  thf('196', plain,
% 35.40/35.61      ((((k2_funct_1 @ sk_C)
% 35.40/35.61          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 35.40/35.61        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 35.40/35.61      inference('demod', [status(thm)], ['184', '195'])).
% 35.40/35.61  thf('197', plain,
% 35.40/35.61      ((~ (v1_relat_1 @ sk_C)
% 35.40/35.61        | ~ (v1_funct_1 @ sk_C)
% 35.40/35.61        | ((k2_funct_1 @ sk_C)
% 35.40/35.61            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A))))),
% 35.40/35.61      inference('sup-', [status(thm)], ['171', '196'])).
% 35.40/35.61  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 35.40/35.61      inference('sup-', [status(thm)], ['162', '163'])).
% 35.40/35.61  thf('199', plain, ((v1_funct_1 @ sk_C)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('200', plain,
% 35.40/35.61      (((k2_funct_1 @ sk_C)
% 35.40/35.61         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A)))),
% 35.40/35.61      inference('demod', [status(thm)], ['197', '198', '199'])).
% 35.40/35.61  thf('201', plain,
% 35.40/35.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('202', plain,
% 35.40/35.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 35.40/35.61         ((v1_relat_1 @ X10)
% 35.40/35.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 35.40/35.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 35.40/35.61  thf('203', plain, ((v1_relat_1 @ sk_D)),
% 35.40/35.61      inference('sup-', [status(thm)], ['201', '202'])).
% 35.40/35.61  thf('204', plain,
% 35.40/35.61      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 35.40/35.61      inference('demod', [status(thm)], ['170', '200', '203'])).
% 35.40/35.61  thf('205', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 35.40/35.61      inference('demod', [status(thm)], ['35', '39', '40', '41', '42', '43'])).
% 35.40/35.61  thf('206', plain,
% 35.40/35.61      (![X5 : $i]:
% 35.40/35.61         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 35.40/35.61          | ~ (v1_funct_1 @ X5)
% 35.40/35.61          | ~ (v1_relat_1 @ X5))),
% 35.40/35.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 35.40/35.61  thf('207', plain,
% 35.40/35.61      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 35.40/35.61      inference('simplify_reflect-', [status(thm)], ['180', '181'])).
% 35.40/35.61  thf('208', plain,
% 35.40/35.61      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 35.40/35.61      inference('simplify_reflect-', [status(thm)], ['157', '158'])).
% 35.40/35.61  thf('209', plain,
% 35.40/35.61      (![X5 : $i]:
% 35.40/35.61         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 35.40/35.61          | ~ (v1_funct_1 @ X5)
% 35.40/35.61          | ~ (v1_relat_1 @ X5))),
% 35.40/35.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 35.40/35.61  thf('210', plain,
% 35.40/35.61      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 35.40/35.61      inference('simplify_reflect-', [status(thm)], ['180', '181'])).
% 35.40/35.61  thf('211', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 35.40/35.61              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 35.40/35.61          | ~ (v1_relat_1 @ X2)
% 35.40/35.61          | ~ (v1_relat_1 @ X1))),
% 35.40/35.61      inference('cnf', [status(esa)], [t55_relat_1])).
% 35.40/35.61  thf('212', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 35.40/35.61            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 35.40/35.61          | ~ (v1_relat_1 @ sk_C)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 35.40/35.61      inference('sup+', [status(thm)], ['210', '211'])).
% 35.40/35.61  thf('213', plain, ((v1_relat_1 @ sk_C)),
% 35.40/35.61      inference('sup-', [status(thm)], ['162', '163'])).
% 35.40/35.61  thf('214', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 35.40/35.61            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 35.40/35.61      inference('demod', [status(thm)], ['212', '213'])).
% 35.40/35.61  thf('215', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ sk_C)
% 35.40/35.61          | ~ (v1_funct_1 @ sk_C)
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 35.40/35.61              = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 35.40/35.61      inference('sup-', [status(thm)], ['209', '214'])).
% 35.40/35.61  thf('216', plain, ((v1_relat_1 @ sk_C)),
% 35.40/35.61      inference('sup-', [status(thm)], ['162', '163'])).
% 35.40/35.61  thf('217', plain, ((v1_funct_1 @ sk_C)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('218', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 35.40/35.61              = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 35.40/35.61      inference('demod', [status(thm)], ['215', '216', '217'])).
% 35.40/35.61  thf('219', plain,
% 35.40/35.61      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C)
% 35.40/35.61          = (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))
% 35.40/35.61        | ~ (v1_relat_1 @ sk_C))),
% 35.40/35.61      inference('sup+', [status(thm)], ['208', '218'])).
% 35.40/35.61  thf('220', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 35.40/35.61      inference('sup+', [status(thm)], ['187', '188'])).
% 35.40/35.61  thf('221', plain,
% 35.40/35.61      (![X4 : $i]:
% 35.40/35.61         (((k5_relat_1 @ X4 @ (k6_relat_1 @ (k2_relat_1 @ X4))) = (X4))
% 35.40/35.61          | ~ (v1_relat_1 @ X4))),
% 35.40/35.61      inference('cnf', [status(esa)], [t80_relat_1])).
% 35.40/35.61  thf('222', plain,
% 35.40/35.61      ((((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))
% 35.40/35.61        | ~ (v1_relat_1 @ sk_C))),
% 35.40/35.61      inference('sup+', [status(thm)], ['220', '221'])).
% 35.40/35.61  thf('223', plain, ((v1_relat_1 @ sk_C)),
% 35.40/35.61      inference('sup-', [status(thm)], ['162', '163'])).
% 35.40/35.61  thf('224', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 35.40/35.61      inference('demod', [status(thm)], ['222', '223'])).
% 35.40/35.61  thf('225', plain, ((v1_relat_1 @ sk_C)),
% 35.40/35.61      inference('sup-', [status(thm)], ['162', '163'])).
% 35.40/35.61  thf('226', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) = (sk_C))),
% 35.40/35.61      inference('demod', [status(thm)], ['219', '224', '225'])).
% 35.40/35.61  thf('227', plain,
% 35.40/35.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.40/35.61         (~ (v1_relat_1 @ X0)
% 35.40/35.61          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 35.40/35.61              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 35.40/35.61          | ~ (v1_relat_1 @ X2)
% 35.40/35.61          | ~ (v1_relat_1 @ X1))),
% 35.40/35.61      inference('cnf', [status(esa)], [t55_relat_1])).
% 35.40/35.61  thf('228', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (((k5_relat_1 @ sk_C @ X0)
% 35.40/35.61            = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k5_relat_1 @ sk_C @ X0)))
% 35.40/35.61          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 35.40/35.61          | ~ (v1_relat_1 @ X0)
% 35.40/35.61          | ~ (v1_relat_1 @ sk_C))),
% 35.40/35.61      inference('sup+', [status(thm)], ['226', '227'])).
% 35.40/35.61  thf('229', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 35.40/35.61      inference('cnf', [status(esa)], [fc4_funct_1])).
% 35.40/35.61  thf('230', plain, ((v1_relat_1 @ sk_C)),
% 35.40/35.61      inference('sup-', [status(thm)], ['162', '163'])).
% 35.40/35.61  thf('231', plain,
% 35.40/35.61      (![X0 : $i]:
% 35.40/35.61         (((k5_relat_1 @ sk_C @ X0)
% 35.40/35.61            = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k5_relat_1 @ sk_C @ X0)))
% 35.40/35.61          | ~ (v1_relat_1 @ X0))),
% 35.40/35.61      inference('demod', [status(thm)], ['228', '229', '230'])).
% 35.40/35.61  thf('232', plain,
% 35.40/35.61      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 35.40/35.61          = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k6_relat_1 @ sk_A)))
% 35.40/35.61        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 35.40/35.61      inference('sup+', [status(thm)], ['207', '231'])).
% 35.40/35.61  thf('233', plain,
% 35.40/35.61      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 35.40/35.61      inference('simplify_reflect-', [status(thm)], ['180', '181'])).
% 35.40/35.61  thf('234', plain,
% 35.40/35.61      ((((k6_relat_1 @ sk_A)
% 35.40/35.61          = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k6_relat_1 @ sk_A)))
% 35.40/35.61        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 35.40/35.61      inference('demod', [status(thm)], ['232', '233'])).
% 35.40/35.61  thf('235', plain,
% 35.40/35.61      ((~ (v1_relat_1 @ sk_C)
% 35.40/35.61        | ~ (v1_funct_1 @ sk_C)
% 35.40/35.61        | ((k6_relat_1 @ sk_A)
% 35.40/35.61            = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k6_relat_1 @ sk_A))))),
% 35.40/35.61      inference('sup-', [status(thm)], ['206', '234'])).
% 35.40/35.61  thf('236', plain, ((v1_relat_1 @ sk_C)),
% 35.40/35.61      inference('sup-', [status(thm)], ['162', '163'])).
% 35.40/35.61  thf('237', plain, ((v1_funct_1 @ sk_C)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('238', plain,
% 35.40/35.61      (((k6_relat_1 @ sk_A)
% 35.40/35.61         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k6_relat_1 @ sk_A)))),
% 35.40/35.61      inference('demod', [status(thm)], ['235', '236', '237'])).
% 35.40/35.61  thf('239', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 35.40/35.61      inference('demod', [status(thm)], ['35', '39', '40', '41', '42', '43'])).
% 35.40/35.61  thf('240', plain,
% 35.40/35.61      (![X4 : $i]:
% 35.40/35.61         (((k5_relat_1 @ X4 @ (k6_relat_1 @ (k2_relat_1 @ X4))) = (X4))
% 35.40/35.61          | ~ (v1_relat_1 @ X4))),
% 35.40/35.61      inference('cnf', [status(esa)], [t80_relat_1])).
% 35.40/35.61  thf('241', plain,
% 35.40/35.61      ((((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))
% 35.40/35.61        | ~ (v1_relat_1 @ sk_D))),
% 35.40/35.61      inference('sup+', [status(thm)], ['239', '240'])).
% 35.40/35.61  thf('242', plain, ((v1_relat_1 @ sk_D)),
% 35.40/35.61      inference('sup-', [status(thm)], ['201', '202'])).
% 35.40/35.61  thf('243', plain, (((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))),
% 35.40/35.61      inference('demod', [status(thm)], ['241', '242'])).
% 35.40/35.61  thf('244', plain, ((v1_relat_1 @ sk_D)),
% 35.40/35.61      inference('sup-', [status(thm)], ['201', '202'])).
% 35.40/35.61  thf('245', plain, ((v1_funct_1 @ sk_D)),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('246', plain, ((v1_relat_1 @ sk_D)),
% 35.40/35.61      inference('sup-', [status(thm)], ['201', '202'])).
% 35.40/35.61  thf('247', plain, ((v2_funct_1 @ sk_D)),
% 35.40/35.61      inference('sup-', [status(thm)], ['70', '71'])).
% 35.40/35.61  thf('248', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 35.40/35.61      inference('demod', [status(thm)],
% 35.40/35.61                ['123', '137', '204', '205', '238', '243', '244', '245', 
% 35.40/35.61                 '246', '247'])).
% 35.40/35.61  thf('249', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 35.40/35.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.40/35.61  thf('250', plain, ($false),
% 35.40/35.61      inference('simplify_reflect-', [status(thm)], ['248', '249'])).
% 35.40/35.61  
% 35.40/35.61  % SZS output end Refutation
% 35.40/35.61  
% 35.40/35.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
