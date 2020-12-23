%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YBTjAIsUBM

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:07 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  291 (1549 expanded)
%              Number of leaves         :   48 ( 479 expanded)
%              Depth                    :   22
%              Number of atoms          : 2956 (42317 expanded)
%              Number of equality atoms :  203 (2890 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

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
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ( ( k5_relat_1 @ X52 @ ( k2_funct_1 @ X52 ) )
        = ( k6_partfun1 @ X53 ) )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X53 @ X51 @ X52 )
       != X51 ) ) ),
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
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ( ( k5_relat_1 @ X52 @ ( k2_funct_1 @ X52 ) )
        = ( k6_relat_1 @ X53 ) )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X53 @ X51 @ X52 )
       != X51 ) ) ),
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

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('60',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ( ( k5_relat_1 @ X52 @ ( k2_funct_1 @ X52 ) )
        = ( k6_relat_1 @ X53 ) )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X53 @ X51 @ X52 )
       != X51 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('63',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf(fc7_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B )
        & ( v2_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v2_funct_1 @ X3 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_funct_1])).

thf('73',plain,
    ( ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('75',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X50 @ X49 @ X48 )
       != X49 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X50 @ X49 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X50 @ X49 @ X48 )
       != X49 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X50 @ X49 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('85',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['85','86','87','88','89'])).

thf('91',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('92',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('93',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['73','82','93','96','97','98'])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['59','104','105','106','107','108'])).

thf('110',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('112',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v2_funct_1 @ X40 )
      | ~ ( zip_tseitin_0 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('116',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['51','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
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

thf('120',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['118','123'])).

thf('125',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('127',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['124','125','126'])).

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

thf('128',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k2_funct_1 @ X8 ) )
      | ( ( k5_relat_1 @ X7 @ X8 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('129',plain,
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
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['35','39','40','41','42','43'])).

thf('131',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('133',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('137',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('142',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['129','130','133','134','139','140','141'])).

thf('143',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['114','115'])).

thf('145',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['51','116'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('147',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('148',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X52 ) @ X52 )
        = ( k6_partfun1 @ X51 ) )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X53 @ X51 @ X52 )
       != X51 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('151',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('152',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X52 ) @ X52 )
        = ( k6_relat_1 @ X51 ) )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X53 @ X51 @ X52 )
       != X51 ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['149','152'])).

thf('154',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['153','154','155','156','157'])).

thf('159',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['159','160'])).

thf(t59_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('162',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 ) )
        = ( k2_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('163',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['137','138'])).

thf('165',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('166',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['163','164','165','166','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['131','132'])).

thf('170',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['114','115'])).

thf('172',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['148','168','169','170','171'])).

thf('173',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['145','172'])).

thf('174',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['117','174'])).

thf('176',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['35','39','40','41','42','43'])).

thf('177',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['137','138'])).

thf('178',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k2_funct_1 @ X8 ) )
      | ( ( k5_relat_1 @ X7 @ X8 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_C )
       != ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_C )
       != ( k6_relat_1 @ sk_B ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['179','180','181','182'])).

thf('184',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
     != ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['176','183'])).

thf('185',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['131','132'])).

thf('186',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
     != ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
     != ( k6_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['187','188'])).

thf('190',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('191',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('192',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['81'])).

thf('194',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('195',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('197',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
      = sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('199',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('200',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('201',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('203',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('204',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['81'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('205',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('206',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X9 ) )
        = X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('207',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 ) )
        = ( k2_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['205','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['204','210'])).

thf('212',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('213',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['211','212','213','214'])).

thf('216',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['203','215'])).

thf('217',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('218',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['216','217','218','219'])).

thf('221',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['202','220'])).

thf('222',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('223',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['221','222','223','224'])).

thf('226',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['201','225'])).

thf('227',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('228',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X50 @ X49 @ X48 )
       != X49 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X48 ) @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X50 @ X49 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('230',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['230','231','232','233','234'])).

thf('236',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['235'])).

thf('237',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['81'])).

thf('238',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['197','198','226','227','236','237'])).

thf('239',plain,
    ( ( sk_A != sk_A )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
     != ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['189','238'])).

thf('240',plain,(
    ( k5_relat_1 @ sk_D @ sk_C )
 != ( k6_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['175','240'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YBTjAIsUBM
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.96  % Solved by: fo/fo7.sh
% 0.76/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.96  % done 1007 iterations in 0.502s
% 0.76/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.96  % SZS output start Refutation
% 0.76/0.96  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.76/0.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.96  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.76/0.96  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.76/0.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.76/0.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.96  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.76/0.96  thf(sk_D_type, type, sk_D: $i).
% 0.76/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.96  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.76/0.96  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.76/0.96  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.96  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.96  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.76/0.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.96  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.76/0.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.96  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.76/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.96  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.76/0.96  thf(t36_funct_2, conjecture,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.96       ( ![D:$i]:
% 0.76/0.96         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.76/0.96             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.76/0.96           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.76/0.96               ( r2_relset_1 @
% 0.76/0.96                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.76/0.96                 ( k6_partfun1 @ A ) ) & 
% 0.76/0.96               ( v2_funct_1 @ C ) ) =>
% 0.76/0.96             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.76/0.96               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.76/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.96    (~( ![A:$i,B:$i,C:$i]:
% 0.76/0.96        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.96            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.96          ( ![D:$i]:
% 0.76/0.96            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.76/0.96                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.76/0.96              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.76/0.96                  ( r2_relset_1 @
% 0.76/0.96                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.76/0.96                    ( k6_partfun1 @ A ) ) & 
% 0.76/0.96                  ( v2_funct_1 @ C ) ) =>
% 0.76/0.96                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.76/0.96                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.76/0.96    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.76/0.96  thf('0', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(t35_funct_2, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.96       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.76/0.96         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.76/0.96           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.76/0.96             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.76/0.96  thf('1', plain,
% 0.76/0.96      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.76/0.96         (((X51) = (k1_xboole_0))
% 0.76/0.96          | ~ (v1_funct_1 @ X52)
% 0.76/0.96          | ~ (v1_funct_2 @ X52 @ X53 @ X51)
% 0.76/0.96          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 0.76/0.96          | ((k5_relat_1 @ X52 @ (k2_funct_1 @ X52)) = (k6_partfun1 @ X53))
% 0.76/0.96          | ~ (v2_funct_1 @ X52)
% 0.76/0.96          | ((k2_relset_1 @ X53 @ X51 @ X52) != (X51)))),
% 0.76/0.96      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.76/0.96  thf(redefinition_k6_partfun1, axiom,
% 0.76/0.96    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.76/0.96  thf('2', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.76/0.96  thf('3', plain,
% 0.76/0.96      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.76/0.96         (((X51) = (k1_xboole_0))
% 0.76/0.96          | ~ (v1_funct_1 @ X52)
% 0.76/0.96          | ~ (v1_funct_2 @ X52 @ X53 @ X51)
% 0.76/0.96          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 0.76/0.96          | ((k5_relat_1 @ X52 @ (k2_funct_1 @ X52)) = (k6_relat_1 @ X53))
% 0.76/0.96          | ~ (v2_funct_1 @ X52)
% 0.76/0.96          | ((k2_relset_1 @ X53 @ X51 @ X52) != (X51)))),
% 0.76/0.96      inference('demod', [status(thm)], ['1', '2'])).
% 0.76/0.96  thf('4', plain,
% 0.76/0.96      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.76/0.96        | ~ (v2_funct_1 @ sk_D)
% 0.76/0.96        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.76/0.96        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.76/0.96        | ~ (v1_funct_1 @ sk_D)
% 0.76/0.96        | ((sk_A) = (k1_xboole_0)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['0', '3'])).
% 0.76/0.96  thf('5', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(redefinition_k2_relset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.76/0.96  thf('6', plain,
% 0.76/0.96      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.76/0.96         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.76/0.96          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.76/0.96  thf('7', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.76/0.96      inference('sup-', [status(thm)], ['5', '6'])).
% 0.76/0.96  thf('8', plain,
% 0.76/0.96      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.96        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.76/0.96        (k6_partfun1 @ sk_A))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('9', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.76/0.96  thf('10', plain,
% 0.76/0.96      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.96        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.76/0.96        (k6_relat_1 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['8', '9'])).
% 0.76/0.96  thf('11', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('12', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(dt_k1_partfun1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.76/0.96     ( ( ( v1_funct_1 @ E ) & 
% 0.76/0.96         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.76/0.96         ( v1_funct_1 @ F ) & 
% 0.76/0.96         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.76/0.96       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.76/0.96         ( m1_subset_1 @
% 0.76/0.96           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.76/0.96           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.76/0.96  thf('13', plain,
% 0.76/0.96      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.76/0.96          | ~ (v1_funct_1 @ X20)
% 0.76/0.96          | ~ (v1_funct_1 @ X23)
% 0.76/0.96          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.76/0.96          | (m1_subset_1 @ (k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23) @ 
% 0.76/0.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X25))))),
% 0.76/0.96      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.76/0.96  thf('14', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.96         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.76/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.76/0.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.76/0.96          | ~ (v1_funct_1 @ X1)
% 0.76/0.96          | ~ (v1_funct_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['12', '13'])).
% 0.76/0.96  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('16', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.96         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.76/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.76/0.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.76/0.96          | ~ (v1_funct_1 @ X1))),
% 0.76/0.96      inference('demod', [status(thm)], ['14', '15'])).
% 0.76/0.96  thf('17', plain,
% 0.76/0.96      ((~ (v1_funct_1 @ sk_D)
% 0.76/0.96        | (m1_subset_1 @ 
% 0.76/0.96           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.76/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['11', '16'])).
% 0.76/0.96  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('19', plain,
% 0.76/0.96      ((m1_subset_1 @ 
% 0.76/0.96        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.76/0.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.96      inference('demod', [status(thm)], ['17', '18'])).
% 0.76/0.96  thf(redefinition_r2_relset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.96     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.76/0.96         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.96       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.76/0.96  thf('20', plain,
% 0.76/0.96      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.76/0.96          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.76/0.96          | ((X16) = (X19))
% 0.76/0.96          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.76/0.96  thf('21', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.96             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.76/0.96          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.76/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['19', '20'])).
% 0.76/0.96  thf('22', plain,
% 0.76/0.96      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.76/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.76/0.96        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.76/0.96            = (k6_relat_1 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['10', '21'])).
% 0.76/0.96  thf(dt_k6_partfun1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( m1_subset_1 @
% 0.76/0.96         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.76/0.96       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.76/0.96  thf('23', plain,
% 0.76/0.96      (![X27 : $i]:
% 0.76/0.96         (m1_subset_1 @ (k6_partfun1 @ X27) @ 
% 0.76/0.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.76/0.96      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.76/0.96  thf('24', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.76/0.96  thf('25', plain,
% 0.76/0.96      (![X27 : $i]:
% 0.76/0.96         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 0.76/0.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.76/0.96      inference('demod', [status(thm)], ['23', '24'])).
% 0.76/0.96  thf('26', plain,
% 0.76/0.96      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.76/0.96         = (k6_relat_1 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['22', '25'])).
% 0.76/0.96  thf('27', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(t24_funct_2, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.96       ( ![D:$i]:
% 0.76/0.96         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.76/0.96             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.76/0.96           ( ( r2_relset_1 @
% 0.76/0.96               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.76/0.96               ( k6_partfun1 @ B ) ) =>
% 0.76/0.96             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.76/0.96  thf('28', plain,
% 0.76/0.96      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.76/0.96         (~ (v1_funct_1 @ X35)
% 0.76/0.96          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 0.76/0.96          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.76/0.96          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 0.76/0.96               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 0.76/0.96               (k6_partfun1 @ X36))
% 0.76/0.96          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 0.76/0.96          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.76/0.96          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 0.76/0.96          | ~ (v1_funct_1 @ X38))),
% 0.76/0.96      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.76/0.96  thf('29', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.76/0.96  thf('30', plain,
% 0.76/0.96      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.76/0.96         (~ (v1_funct_1 @ X35)
% 0.76/0.96          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 0.76/0.96          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.76/0.96          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 0.76/0.96               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 0.76/0.96               (k6_relat_1 @ X36))
% 0.76/0.96          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 0.76/0.96          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.76/0.96          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 0.76/0.96          | ~ (v1_funct_1 @ X38))),
% 0.76/0.96      inference('demod', [status(thm)], ['28', '29'])).
% 0.76/0.96  thf('31', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (v1_funct_1 @ X0)
% 0.76/0.96          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.76/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.76/0.96          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.76/0.96          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.96               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.76/0.96               (k6_relat_1 @ sk_A))
% 0.76/0.96          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.76/0.96          | ~ (v1_funct_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['27', '30'])).
% 0.76/0.96  thf('32', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('34', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (v1_funct_1 @ X0)
% 0.76/0.96          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.76/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.76/0.96          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.76/0.96          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.96               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.76/0.96               (k6_relat_1 @ sk_A)))),
% 0.76/0.96      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.76/0.96  thf('35', plain,
% 0.76/0.96      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.76/0.96           (k6_relat_1 @ sk_A))
% 0.76/0.96        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.76/0.96        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.76/0.96        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.76/0.96        | ~ (v1_funct_1 @ sk_D))),
% 0.76/0.96      inference('sup-', [status(thm)], ['26', '34'])).
% 0.76/0.96  thf('36', plain,
% 0.76/0.96      (![X27 : $i]:
% 0.76/0.96         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 0.76/0.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.76/0.96      inference('demod', [status(thm)], ['23', '24'])).
% 0.76/0.96  thf('37', plain,
% 0.76/0.96      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.76/0.96          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.76/0.96          | (r2_relset_1 @ X17 @ X18 @ X16 @ X19)
% 0.76/0.96          | ((X16) != (X19)))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.76/0.96  thf('38', plain,
% 0.76/0.96      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.76/0.96         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 0.76/0.96          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.76/0.96      inference('simplify', [status(thm)], ['37'])).
% 0.76/0.96  thf('39', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['36', '38'])).
% 0.76/0.96  thf('40', plain,
% 0.76/0.96      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.76/0.96      inference('sup-', [status(thm)], ['5', '6'])).
% 0.76/0.96  thf('41', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('42', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('44', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['35', '39', '40', '41', '42', '43'])).
% 0.76/0.96  thf('45', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['7', '44'])).
% 0.76/0.96  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('48', plain,
% 0.76/0.96      ((((sk_A) != (sk_A))
% 0.76/0.96        | ~ (v2_funct_1 @ sk_D)
% 0.76/0.96        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.76/0.96        | ((sk_A) = (k1_xboole_0)))),
% 0.76/0.96      inference('demod', [status(thm)], ['4', '45', '46', '47'])).
% 0.76/0.96  thf('49', plain,
% 0.76/0.96      ((((sk_A) = (k1_xboole_0))
% 0.76/0.96        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.76/0.96        | ~ (v2_funct_1 @ sk_D))),
% 0.76/0.96      inference('simplify', [status(thm)], ['48'])).
% 0.76/0.96  thf('50', plain, (((sk_A) != (k1_xboole_0))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('51', plain,
% 0.76/0.96      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.76/0.96        | ~ (v2_funct_1 @ sk_D))),
% 0.76/0.96      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.76/0.96  thf('52', plain,
% 0.76/0.96      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.76/0.96         = (k6_relat_1 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['22', '25'])).
% 0.76/0.96  thf('53', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(t30_funct_2, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.96     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.76/0.96         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.76/0.96       ( ![E:$i]:
% 0.76/0.96         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 0.76/0.96             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 0.76/0.96           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.76/0.96               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 0.76/0.96             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 0.76/0.96               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.76/0.96  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.76/0.96  thf(zf_stmt_2, axiom,
% 0.76/0.96    (![C:$i,B:$i]:
% 0.76/0.96     ( ( zip_tseitin_1 @ C @ B ) =>
% 0.76/0.96       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.76/0.96  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.76/0.96  thf(zf_stmt_4, axiom,
% 0.76/0.96    (![E:$i,D:$i]:
% 0.76/0.96     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 0.76/0.96  thf(zf_stmt_5, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.96     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.76/0.96         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.96       ( ![E:$i]:
% 0.76/0.96         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.76/0.96             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.76/0.96           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 0.76/0.96               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 0.76/0.96             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 0.76/0.96  thf('54', plain,
% 0.76/0.96      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.76/0.96         (~ (v1_funct_1 @ X43)
% 0.76/0.96          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 0.76/0.96          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.76/0.96          | (zip_tseitin_0 @ X43 @ X46)
% 0.76/0.96          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X44 @ X44 @ X45 @ X46 @ X43))
% 0.76/0.96          | (zip_tseitin_1 @ X45 @ X44)
% 0.76/0.96          | ((k2_relset_1 @ X47 @ X44 @ X46) != (X44))
% 0.76/0.96          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X44)))
% 0.76/0.96          | ~ (v1_funct_2 @ X46 @ X47 @ X44)
% 0.76/0.96          | ~ (v1_funct_1 @ X46))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.96  thf('55', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         (~ (v1_funct_1 @ X0)
% 0.76/0.96          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.76/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.76/0.96          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.76/0.96          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.76/0.96          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.76/0.96          | (zip_tseitin_0 @ sk_D @ X0)
% 0.76/0.96          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.76/0.96          | ~ (v1_funct_1 @ sk_D))),
% 0.76/0.96      inference('sup-', [status(thm)], ['53', '54'])).
% 0.76/0.96  thf('56', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('58', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         (~ (v1_funct_1 @ X0)
% 0.76/0.96          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.76/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.76/0.96          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.76/0.96          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.76/0.96          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.76/0.96          | (zip_tseitin_0 @ sk_D @ X0))),
% 0.76/0.96      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.76/0.96  thf('59', plain,
% 0.76/0.96      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.76/0.96        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.76/0.96        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.76/0.96        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.76/0.96        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.76/0.96        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.76/0.96        | ~ (v1_funct_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['52', '58'])).
% 0.76/0.96  thf(fc6_funct_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.76/0.96       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.76/0.96         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.76/0.96         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.76/0.96  thf('60', plain,
% 0.76/0.96      (![X1 : $i]:
% 0.76/0.96         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 0.76/0.96          | ~ (v2_funct_1 @ X1)
% 0.76/0.96          | ~ (v1_funct_1 @ X1)
% 0.76/0.96          | ~ (v1_relat_1 @ X1))),
% 0.76/0.96      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.76/0.96  thf('61', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('62', plain,
% 0.76/0.96      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.76/0.96         (((X51) = (k1_xboole_0))
% 0.76/0.96          | ~ (v1_funct_1 @ X52)
% 0.76/0.96          | ~ (v1_funct_2 @ X52 @ X53 @ X51)
% 0.76/0.96          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 0.76/0.96          | ((k5_relat_1 @ X52 @ (k2_funct_1 @ X52)) = (k6_relat_1 @ X53))
% 0.76/0.96          | ~ (v2_funct_1 @ X52)
% 0.76/0.96          | ((k2_relset_1 @ X53 @ X51 @ X52) != (X51)))),
% 0.76/0.96      inference('demod', [status(thm)], ['1', '2'])).
% 0.76/0.96  thf('63', plain,
% 0.76/0.96      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.76/0.96        | ~ (v2_funct_1 @ sk_C)
% 0.76/0.96        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 0.76/0.96        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.76/0.96        | ~ (v1_funct_1 @ sk_C)
% 0.76/0.96        | ((sk_B) = (k1_xboole_0)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['61', '62'])).
% 0.76/0.96  thf('64', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('65', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('66', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('68', plain,
% 0.76/0.96      ((((sk_B) != (sk_B))
% 0.76/0.96        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 0.76/0.96        | ((sk_B) = (k1_xboole_0)))),
% 0.76/0.96      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.76/0.96  thf('69', plain,
% 0.76/0.96      ((((sk_B) = (k1_xboole_0))
% 0.76/0.96        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 0.76/0.96      inference('simplify', [status(thm)], ['68'])).
% 0.76/0.96  thf('70', plain, (((sk_B) != (k1_xboole_0))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('71', plain,
% 0.76/0.96      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 0.76/0.96      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 0.76/0.96  thf(fc7_funct_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) & 
% 0.76/0.96         ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) & ( v2_funct_1 @ B ) ) =>
% 0.76/0.96       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.76/0.96         ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.76/0.96  thf('72', plain,
% 0.76/0.96      (![X2 : $i, X3 : $i]:
% 0.76/0.96         (~ (v2_funct_1 @ X2)
% 0.76/0.96          | ~ (v1_funct_1 @ X2)
% 0.76/0.96          | ~ (v1_relat_1 @ X2)
% 0.76/0.96          | ~ (v1_relat_1 @ X3)
% 0.76/0.96          | ~ (v1_funct_1 @ X3)
% 0.76/0.96          | ~ (v2_funct_1 @ X3)
% 0.76/0.96          | (v2_funct_1 @ (k5_relat_1 @ X2 @ X3)))),
% 0.76/0.96      inference('cnf', [status(esa)], [fc7_funct_1])).
% 0.76/0.96  thf('73', plain,
% 0.76/0.96      (((v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.76/0.96        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.76/0.96        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.76/0.96        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.76/0.96        | ~ (v1_relat_1 @ sk_C)
% 0.76/0.96        | ~ (v1_funct_1 @ sk_C)
% 0.76/0.96        | ~ (v2_funct_1 @ sk_C))),
% 0.76/0.96      inference('sup+', [status(thm)], ['71', '72'])).
% 0.76/0.96  thf('74', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(t31_funct_2, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.96       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.76/0.96         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.76/0.96           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.76/0.96           ( m1_subset_1 @
% 0.76/0.96             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.76/0.96  thf('75', plain,
% 0.76/0.96      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.76/0.96         (~ (v2_funct_1 @ X48)
% 0.76/0.96          | ((k2_relset_1 @ X50 @ X49 @ X48) != (X49))
% 0.76/0.96          | (v1_funct_1 @ (k2_funct_1 @ X48))
% 0.76/0.96          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 0.76/0.96          | ~ (v1_funct_2 @ X48 @ X50 @ X49)
% 0.76/0.96          | ~ (v1_funct_1 @ X48))),
% 0.76/0.96      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.76/0.96  thf('76', plain,
% 0.76/0.96      ((~ (v1_funct_1 @ sk_C)
% 0.76/0.96        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.76/0.96        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.76/0.96        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.76/0.96        | ~ (v2_funct_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['74', '75'])).
% 0.76/0.96  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('78', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('79', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('80', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('81', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)) | ((sk_B) != (sk_B)))),
% 0.76/0.96      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.76/0.96  thf('82', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.76/0.96      inference('simplify', [status(thm)], ['81'])).
% 0.76/0.96  thf('83', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('84', plain,
% 0.76/0.96      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.76/0.96         (~ (v2_funct_1 @ X48)
% 0.76/0.96          | ((k2_relset_1 @ X50 @ X49 @ X48) != (X49))
% 0.76/0.96          | (m1_subset_1 @ (k2_funct_1 @ X48) @ 
% 0.76/0.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 0.76/0.96          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 0.76/0.96          | ~ (v1_funct_2 @ X48 @ X50 @ X49)
% 0.76/0.96          | ~ (v1_funct_1 @ X48))),
% 0.76/0.96      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.76/0.96  thf('85', plain,
% 0.76/0.96      ((~ (v1_funct_1 @ sk_C)
% 0.76/0.96        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.76/0.96        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.76/0.96        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.76/0.96        | ~ (v2_funct_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['83', '84'])).
% 0.76/0.96  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('87', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('88', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('89', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('90', plain,
% 0.76/0.96      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/0.96         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.76/0.96        | ((sk_B) != (sk_B)))),
% 0.76/0.96      inference('demod', [status(thm)], ['85', '86', '87', '88', '89'])).
% 0.76/0.96  thf('91', plain,
% 0.76/0.96      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/0.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.76/0.96      inference('simplify', [status(thm)], ['90'])).
% 0.76/0.96  thf(cc1_relset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( v1_relat_1 @ C ) ))).
% 0.76/0.96  thf('92', plain,
% 0.76/0.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.76/0.96         ((v1_relat_1 @ X10)
% 0.76/0.96          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.76/0.96      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.76/0.96  thf('93', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['91', '92'])).
% 0.76/0.96  thf('94', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('95', plain,
% 0.76/0.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.76/0.96         ((v1_relat_1 @ X10)
% 0.76/0.96          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.76/0.96      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.76/0.96  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.96      inference('sup-', [status(thm)], ['94', '95'])).
% 0.76/0.96  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('99', plain,
% 0.76/0.96      (((v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.76/0.96        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/0.96      inference('demod', [status(thm)], ['73', '82', '93', '96', '97', '98'])).
% 0.76/0.96  thf('100', plain,
% 0.76/0.96      ((~ (v1_relat_1 @ sk_C)
% 0.76/0.96        | ~ (v1_funct_1 @ sk_C)
% 0.76/0.96        | ~ (v2_funct_1 @ sk_C)
% 0.76/0.96        | (v2_funct_1 @ (k6_relat_1 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['60', '99'])).
% 0.76/0.96  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.96      inference('sup-', [status(thm)], ['94', '95'])).
% 0.76/0.96  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('103', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('104', plain, ((v2_funct_1 @ (k6_relat_1 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 0.76/0.96  thf('105', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('106', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('107', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('109', plain,
% 0.76/0.96      (((zip_tseitin_0 @ sk_D @ sk_C)
% 0.76/0.96        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.76/0.96        | ((sk_B) != (sk_B)))),
% 0.76/0.96      inference('demod', [status(thm)],
% 0.76/0.96                ['59', '104', '105', '106', '107', '108'])).
% 0.76/0.96  thf('110', plain,
% 0.76/0.96      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 0.76/0.96      inference('simplify', [status(thm)], ['109'])).
% 0.76/0.96  thf('111', plain,
% 0.76/0.96      (![X41 : $i, X42 : $i]:
% 0.76/0.96         (((X41) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X41 @ X42))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/0.96  thf('112', plain,
% 0.76/0.96      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['110', '111'])).
% 0.76/0.96  thf('113', plain, (((sk_A) != (k1_xboole_0))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('114', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 0.76/0.96      inference('simplify_reflect-', [status(thm)], ['112', '113'])).
% 0.76/0.96  thf('115', plain,
% 0.76/0.96      (![X39 : $i, X40 : $i]:
% 0.76/0.96         ((v2_funct_1 @ X40) | ~ (zip_tseitin_0 @ X40 @ X39))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.76/0.96  thf('116', plain, ((v2_funct_1 @ sk_D)),
% 0.76/0.96      inference('sup-', [status(thm)], ['114', '115'])).
% 0.76/0.96  thf('117', plain,
% 0.76/0.96      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 0.76/0.96      inference('demod', [status(thm)], ['51', '116'])).
% 0.76/0.96  thf('118', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('119', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(redefinition_k1_partfun1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.76/0.96     ( ( ( v1_funct_1 @ E ) & 
% 0.76/0.96         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.76/0.96         ( v1_funct_1 @ F ) & 
% 0.76/0.96         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.76/0.96       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.76/0.96  thf('120', plain,
% 0.76/0.96      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.76/0.96          | ~ (v1_funct_1 @ X28)
% 0.76/0.96          | ~ (v1_funct_1 @ X31)
% 0.76/0.96          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.76/0.96          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 0.76/0.96              = (k5_relat_1 @ X28 @ X31)))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.76/0.96  thf('121', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.96         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.76/0.96            = (k5_relat_1 @ sk_C @ X0))
% 0.76/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.76/0.96          | ~ (v1_funct_1 @ X0)
% 0.76/0.96          | ~ (v1_funct_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['119', '120'])).
% 0.76/0.96  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('123', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.96         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.76/0.96            = (k5_relat_1 @ sk_C @ X0))
% 0.76/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.76/0.96          | ~ (v1_funct_1 @ X0))),
% 0.76/0.96      inference('demod', [status(thm)], ['121', '122'])).
% 0.76/0.96  thf('124', plain,
% 0.76/0.96      ((~ (v1_funct_1 @ sk_D)
% 0.76/0.96        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.76/0.96            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['118', '123'])).
% 0.76/0.96  thf('125', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('126', plain,
% 0.76/0.96      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.76/0.96         = (k6_relat_1 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['22', '25'])).
% 0.76/0.96  thf('127', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.76/0.96      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.76/0.96  thf(t64_funct_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.76/0.96           ( ( ( v2_funct_1 @ A ) & 
% 0.76/0.96               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.76/0.96               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.76/0.96             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.76/0.96  thf('128', plain,
% 0.76/0.96      (![X7 : $i, X8 : $i]:
% 0.76/0.96         (~ (v1_relat_1 @ X7)
% 0.76/0.96          | ~ (v1_funct_1 @ X7)
% 0.76/0.96          | ((X7) = (k2_funct_1 @ X8))
% 0.76/0.96          | ((k5_relat_1 @ X7 @ X8) != (k6_relat_1 @ (k2_relat_1 @ X8)))
% 0.76/0.96          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.76/0.96          | ~ (v2_funct_1 @ X8)
% 0.76/0.96          | ~ (v1_funct_1 @ X8)
% 0.76/0.96          | ~ (v1_relat_1 @ X8))),
% 0.76/0.96      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.76/0.96  thf('129', plain,
% 0.76/0.96      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 0.76/0.96        | ~ (v1_relat_1 @ sk_D)
% 0.76/0.96        | ~ (v1_funct_1 @ sk_D)
% 0.76/0.96        | ~ (v2_funct_1 @ sk_D)
% 0.76/0.96        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.76/0.96        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.76/0.96        | ~ (v1_funct_1 @ sk_C)
% 0.76/0.96        | ~ (v1_relat_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['127', '128'])).
% 0.76/0.96  thf('130', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['35', '39', '40', '41', '42', '43'])).
% 0.76/0.96  thf('131', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('132', plain,
% 0.76/0.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.76/0.96         ((v1_relat_1 @ X10)
% 0.76/0.96          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.76/0.96      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.76/0.96  thf('133', plain, ((v1_relat_1 @ sk_D)),
% 0.76/0.96      inference('sup-', [status(thm)], ['131', '132'])).
% 0.76/0.96  thf('134', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('135', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('136', plain,
% 0.76/0.96      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.76/0.96         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.76/0.96          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.76/0.96  thf('137', plain,
% 0.76/0.96      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['135', '136'])).
% 0.76/0.96  thf('138', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('139', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['137', '138'])).
% 0.76/0.96  thf('140', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('141', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.96      inference('sup-', [status(thm)], ['94', '95'])).
% 0.76/0.96  thf('142', plain,
% 0.76/0.96      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 0.76/0.96        | ~ (v2_funct_1 @ sk_D)
% 0.76/0.96        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.76/0.96        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.76/0.96      inference('demod', [status(thm)],
% 0.76/0.96                ['129', '130', '133', '134', '139', '140', '141'])).
% 0.76/0.96  thf('143', plain,
% 0.76/0.96      ((((sk_C) = (k2_funct_1 @ sk_D))
% 0.76/0.96        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.76/0.96        | ~ (v2_funct_1 @ sk_D))),
% 0.76/0.96      inference('simplify', [status(thm)], ['142'])).
% 0.76/0.96  thf('144', plain, ((v2_funct_1 @ sk_D)),
% 0.76/0.96      inference('sup-', [status(thm)], ['114', '115'])).
% 0.76/0.96  thf('145', plain,
% 0.76/0.96      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 0.76/0.96      inference('demod', [status(thm)], ['143', '144'])).
% 0.76/0.96  thf('146', plain,
% 0.76/0.96      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 0.76/0.96      inference('demod', [status(thm)], ['51', '116'])).
% 0.76/0.96  thf(t58_funct_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.96       ( ( v2_funct_1 @ A ) =>
% 0.76/0.96         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.76/0.96             ( k1_relat_1 @ A ) ) & 
% 0.76/0.96           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.76/0.96             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.76/0.96  thf('147', plain,
% 0.76/0.96      (![X5 : $i]:
% 0.76/0.96         (~ (v2_funct_1 @ X5)
% 0.76/0.96          | ((k2_relat_1 @ (k5_relat_1 @ X5 @ (k2_funct_1 @ X5)))
% 0.76/0.96              = (k1_relat_1 @ X5))
% 0.76/0.96          | ~ (v1_funct_1 @ X5)
% 0.76/0.96          | ~ (v1_relat_1 @ X5))),
% 0.76/0.96      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.76/0.96  thf('148', plain,
% 0.76/0.96      ((((k2_relat_1 @ (k6_relat_1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 0.76/0.96        | ~ (v1_relat_1 @ sk_D)
% 0.76/0.96        | ~ (v1_funct_1 @ sk_D)
% 0.76/0.96        | ~ (v2_funct_1 @ sk_D))),
% 0.76/0.96      inference('sup+', [status(thm)], ['146', '147'])).
% 0.76/0.96  thf('149', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('150', plain,
% 0.76/0.96      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.76/0.96         (((X51) = (k1_xboole_0))
% 0.76/0.96          | ~ (v1_funct_1 @ X52)
% 0.76/0.96          | ~ (v1_funct_2 @ X52 @ X53 @ X51)
% 0.76/0.96          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 0.76/0.96          | ((k5_relat_1 @ (k2_funct_1 @ X52) @ X52) = (k6_partfun1 @ X51))
% 0.76/0.96          | ~ (v2_funct_1 @ X52)
% 0.76/0.96          | ((k2_relset_1 @ X53 @ X51 @ X52) != (X51)))),
% 0.76/0.96      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.76/0.96  thf('151', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.76/0.96  thf('152', plain,
% 0.76/0.96      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.76/0.96         (((X51) = (k1_xboole_0))
% 0.76/0.96          | ~ (v1_funct_1 @ X52)
% 0.76/0.96          | ~ (v1_funct_2 @ X52 @ X53 @ X51)
% 0.76/0.96          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 0.76/0.96          | ((k5_relat_1 @ (k2_funct_1 @ X52) @ X52) = (k6_relat_1 @ X51))
% 0.76/0.96          | ~ (v2_funct_1 @ X52)
% 0.76/0.96          | ((k2_relset_1 @ X53 @ X51 @ X52) != (X51)))),
% 0.76/0.96      inference('demod', [status(thm)], ['150', '151'])).
% 0.76/0.96  thf('153', plain,
% 0.76/0.96      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.76/0.96        | ~ (v2_funct_1 @ sk_C)
% 0.76/0.96        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 0.76/0.96        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.76/0.96        | ~ (v1_funct_1 @ sk_C)
% 0.76/0.96        | ((sk_B) = (k1_xboole_0)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['149', '152'])).
% 0.76/0.96  thf('154', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('155', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('156', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('158', plain,
% 0.76/0.96      ((((sk_B) != (sk_B))
% 0.76/0.96        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 0.76/0.96        | ((sk_B) = (k1_xboole_0)))),
% 0.76/0.96      inference('demod', [status(thm)], ['153', '154', '155', '156', '157'])).
% 0.76/0.96  thf('159', plain,
% 0.76/0.96      ((((sk_B) = (k1_xboole_0))
% 0.76/0.96        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 0.76/0.96      inference('simplify', [status(thm)], ['158'])).
% 0.76/0.96  thf('160', plain, (((sk_B) != (k1_xboole_0))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('161', plain,
% 0.76/0.96      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.76/0.96      inference('simplify_reflect-', [status(thm)], ['159', '160'])).
% 0.76/0.96  thf(t59_funct_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.96       ( ( v2_funct_1 @ A ) =>
% 0.76/0.96         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.76/0.96             ( k2_relat_1 @ A ) ) & 
% 0.76/0.96           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.76/0.96             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.76/0.96  thf('162', plain,
% 0.76/0.96      (![X6 : $i]:
% 0.76/0.96         (~ (v2_funct_1 @ X6)
% 0.76/0.96          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X6) @ X6))
% 0.76/0.96              = (k2_relat_1 @ X6))
% 0.76/0.96          | ~ (v1_funct_1 @ X6)
% 0.76/0.96          | ~ (v1_relat_1 @ X6))),
% 0.76/0.96      inference('cnf', [status(esa)], [t59_funct_1])).
% 0.76/0.96  thf('163', plain,
% 0.76/0.96      ((((k2_relat_1 @ (k6_relat_1 @ sk_B)) = (k2_relat_1 @ sk_C))
% 0.76/0.96        | ~ (v1_relat_1 @ sk_C)
% 0.76/0.96        | ~ (v1_funct_1 @ sk_C)
% 0.76/0.96        | ~ (v2_funct_1 @ sk_C))),
% 0.76/0.96      inference('sup+', [status(thm)], ['161', '162'])).
% 0.76/0.96  thf('164', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['137', '138'])).
% 0.76/0.96  thf('165', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.96      inference('sup-', [status(thm)], ['94', '95'])).
% 0.76/0.96  thf('166', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('167', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('168', plain, (((k2_relat_1 @ (k6_relat_1 @ sk_B)) = (sk_B))),
% 0.76/0.96      inference('demod', [status(thm)], ['163', '164', '165', '166', '167'])).
% 0.76/0.96  thf('169', plain, ((v1_relat_1 @ sk_D)),
% 0.76/0.96      inference('sup-', [status(thm)], ['131', '132'])).
% 0.76/0.96  thf('170', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('171', plain, ((v2_funct_1 @ sk_D)),
% 0.76/0.96      inference('sup-', [status(thm)], ['114', '115'])).
% 0.76/0.96  thf('172', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.76/0.96      inference('demod', [status(thm)], ['148', '168', '169', '170', '171'])).
% 0.76/0.96  thf('173', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 0.76/0.96      inference('demod', [status(thm)], ['145', '172'])).
% 0.76/0.96  thf('174', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.76/0.96      inference('simplify', [status(thm)], ['173'])).
% 0.76/0.96  thf('175', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.76/0.96      inference('demod', [status(thm)], ['117', '174'])).
% 0.76/0.96  thf('176', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['35', '39', '40', '41', '42', '43'])).
% 0.76/0.96  thf('177', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['137', '138'])).
% 0.76/0.96  thf('178', plain,
% 0.76/0.96      (![X7 : $i, X8 : $i]:
% 0.76/0.96         (~ (v1_relat_1 @ X7)
% 0.76/0.96          | ~ (v1_funct_1 @ X7)
% 0.76/0.96          | ((X7) = (k2_funct_1 @ X8))
% 0.76/0.96          | ((k5_relat_1 @ X7 @ X8) != (k6_relat_1 @ (k2_relat_1 @ X8)))
% 0.76/0.96          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.76/0.96          | ~ (v2_funct_1 @ X8)
% 0.76/0.96          | ~ (v1_funct_1 @ X8)
% 0.76/0.96          | ~ (v1_relat_1 @ X8))),
% 0.76/0.96      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.76/0.96  thf('179', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (((k5_relat_1 @ X0 @ sk_C) != (k6_relat_1 @ sk_B))
% 0.76/0.96          | ~ (v1_relat_1 @ sk_C)
% 0.76/0.96          | ~ (v1_funct_1 @ sk_C)
% 0.76/0.96          | ~ (v2_funct_1 @ sk_C)
% 0.76/0.96          | ((k2_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.76/0.96          | ((X0) = (k2_funct_1 @ sk_C))
% 0.76/0.96          | ~ (v1_funct_1 @ X0)
% 0.76/0.96          | ~ (v1_relat_1 @ X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['177', '178'])).
% 0.76/0.96  thf('180', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.96      inference('sup-', [status(thm)], ['94', '95'])).
% 0.76/0.96  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('182', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('183', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (((k5_relat_1 @ X0 @ sk_C) != (k6_relat_1 @ sk_B))
% 0.76/0.97          | ((k2_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.76/0.97          | ((X0) = (k2_funct_1 @ sk_C))
% 0.76/0.97          | ~ (v1_funct_1 @ X0)
% 0.76/0.97          | ~ (v1_relat_1 @ X0))),
% 0.76/0.97      inference('demod', [status(thm)], ['179', '180', '181', '182'])).
% 0.76/0.97  thf('184', plain,
% 0.76/0.97      ((((sk_A) != (k1_relat_1 @ sk_C))
% 0.76/0.97        | ~ (v1_relat_1 @ sk_D)
% 0.76/0.97        | ~ (v1_funct_1 @ sk_D)
% 0.76/0.97        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.76/0.97        | ((k5_relat_1 @ sk_D @ sk_C) != (k6_relat_1 @ sk_B)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['176', '183'])).
% 0.76/0.97  thf('185', plain, ((v1_relat_1 @ sk_D)),
% 0.76/0.97      inference('sup-', [status(thm)], ['131', '132'])).
% 0.76/0.97  thf('186', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('187', plain,
% 0.76/0.97      ((((sk_A) != (k1_relat_1 @ sk_C))
% 0.76/0.97        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.76/0.97        | ((k5_relat_1 @ sk_D @ sk_C) != (k6_relat_1 @ sk_B)))),
% 0.76/0.97      inference('demod', [status(thm)], ['184', '185', '186'])).
% 0.76/0.97  thf('188', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('189', plain,
% 0.76/0.97      ((((sk_A) != (k1_relat_1 @ sk_C))
% 0.76/0.97        | ((k5_relat_1 @ sk_D @ sk_C) != (k6_relat_1 @ sk_B)))),
% 0.76/0.97      inference('simplify_reflect-', [status(thm)], ['187', '188'])).
% 0.76/0.97  thf('190', plain,
% 0.76/0.97      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/0.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.76/0.97      inference('simplify', [status(thm)], ['90'])).
% 0.76/0.97  thf('191', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.76/0.97            = (k5_relat_1 @ sk_C @ X0))
% 0.76/0.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.76/0.97          | ~ (v1_funct_1 @ X0))),
% 0.76/0.97      inference('demod', [status(thm)], ['121', '122'])).
% 0.76/0.97  thf('192', plain,
% 0.76/0.97      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.76/0.97        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 0.76/0.97            (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['190', '191'])).
% 0.76/0.97  thf('193', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.76/0.97      inference('simplify', [status(thm)], ['81'])).
% 0.76/0.97  thf('194', plain,
% 0.76/0.97      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 0.76/0.97      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 0.76/0.97  thf('195', plain,
% 0.76/0.97      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C))
% 0.76/0.97         = (k6_relat_1 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['192', '193', '194'])).
% 0.76/0.97  thf('196', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (v1_funct_1 @ X0)
% 0.76/0.97          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.76/0.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.76/0.97          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.76/0.97          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.76/0.97               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.76/0.97               (k6_relat_1 @ sk_A)))),
% 0.76/0.97      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.76/0.97  thf('197', plain,
% 0.76/0.97      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.76/0.97           (k6_relat_1 @ sk_A))
% 0.76/0.97        | ((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) = (sk_A))
% 0.76/0.97        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/0.97             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.76/0.97        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.76/0.97        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['195', '196'])).
% 0.76/0.97  thf('198', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['36', '38'])).
% 0.76/0.97  thf('199', plain,
% 0.76/0.97      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/0.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.76/0.97      inference('simplify', [status(thm)], ['90'])).
% 0.76/0.97  thf('200', plain,
% 0.76/0.97      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.76/0.97         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.76/0.97          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.76/0.97      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.76/0.97  thf('201', plain,
% 0.76/0.97      (((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C))
% 0.76/0.97         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['199', '200'])).
% 0.76/0.97  thf('202', plain,
% 0.76/0.97      (![X5 : $i]:
% 0.76/0.97         (~ (v2_funct_1 @ X5)
% 0.76/0.97          | ((k2_relat_1 @ (k5_relat_1 @ X5 @ (k2_funct_1 @ X5)))
% 0.76/0.97              = (k1_relat_1 @ X5))
% 0.76/0.97          | ~ (v1_funct_1 @ X5)
% 0.76/0.97          | ~ (v1_relat_1 @ X5))),
% 0.76/0.97      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.76/0.97  thf('203', plain,
% 0.76/0.97      (![X1 : $i]:
% 0.76/0.97         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 0.76/0.97          | ~ (v2_funct_1 @ X1)
% 0.76/0.97          | ~ (v1_funct_1 @ X1)
% 0.76/0.97          | ~ (v1_relat_1 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.76/0.97  thf('204', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.76/0.97      inference('simplify', [status(thm)], ['81'])).
% 0.76/0.97  thf(dt_k2_funct_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.97       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.76/0.97         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.76/0.97  thf('205', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.76/0.97          | ~ (v1_funct_1 @ X0)
% 0.76/0.97          | ~ (v1_relat_1 @ X0))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.76/0.97  thf(t65_funct_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.97       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.76/0.97  thf('206', plain,
% 0.76/0.97      (![X9 : $i]:
% 0.76/0.97         (~ (v2_funct_1 @ X9)
% 0.76/0.97          | ((k2_funct_1 @ (k2_funct_1 @ X9)) = (X9))
% 0.76/0.97          | ~ (v1_funct_1 @ X9)
% 0.76/0.97          | ~ (v1_relat_1 @ X9))),
% 0.76/0.97      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.76/0.97  thf('207', plain,
% 0.76/0.97      (![X6 : $i]:
% 0.76/0.97         (~ (v2_funct_1 @ X6)
% 0.76/0.97          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X6) @ X6))
% 0.76/0.97              = (k2_relat_1 @ X6))
% 0.76/0.97          | ~ (v1_funct_1 @ X6)
% 0.76/0.97          | ~ (v1_relat_1 @ X6))),
% 0.76/0.97      inference('cnf', [status(esa)], [t59_funct_1])).
% 0.76/0.97  thf('208', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.76/0.97            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.76/0.97          | ~ (v1_relat_1 @ X0)
% 0.76/0.97          | ~ (v1_funct_1 @ X0)
% 0.76/0.97          | ~ (v2_funct_1 @ X0)
% 0.76/0.97          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.76/0.97          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.76/0.97          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.76/0.97      inference('sup+', [status(thm)], ['206', '207'])).
% 0.76/0.97  thf('209', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (v1_relat_1 @ X0)
% 0.76/0.97          | ~ (v1_funct_1 @ X0)
% 0.76/0.97          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.76/0.97          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.76/0.97          | ~ (v2_funct_1 @ X0)
% 0.76/0.97          | ~ (v1_funct_1 @ X0)
% 0.76/0.97          | ~ (v1_relat_1 @ X0)
% 0.76/0.97          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.76/0.97              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['205', '208'])).
% 0.76/0.97  thf('210', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.76/0.97            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.76/0.97          | ~ (v2_funct_1 @ X0)
% 0.76/0.97          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.76/0.97          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.76/0.97          | ~ (v1_funct_1 @ X0)
% 0.76/0.97          | ~ (v1_relat_1 @ X0))),
% 0.76/0.97      inference('simplify', [status(thm)], ['209'])).
% 0.76/0.97  thf('211', plain,
% 0.76/0.97      ((~ (v1_relat_1 @ sk_C)
% 0.76/0.97        | ~ (v1_funct_1 @ sk_C)
% 0.76/0.97        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.76/0.97        | ~ (v2_funct_1 @ sk_C)
% 0.76/0.97        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 0.76/0.97            = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['204', '210'])).
% 0.76/0.97  thf('212', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.97      inference('sup-', [status(thm)], ['94', '95'])).
% 0.76/0.97  thf('213', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('214', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('215', plain,
% 0.76/0.97      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.76/0.97        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 0.76/0.97            = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.76/0.97      inference('demod', [status(thm)], ['211', '212', '213', '214'])).
% 0.76/0.97  thf('216', plain,
% 0.76/0.97      ((~ (v1_relat_1 @ sk_C)
% 0.76/0.97        | ~ (v1_funct_1 @ sk_C)
% 0.76/0.97        | ~ (v2_funct_1 @ sk_C)
% 0.76/0.97        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 0.76/0.97            = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['203', '215'])).
% 0.76/0.97  thf('217', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.97      inference('sup-', [status(thm)], ['94', '95'])).
% 0.76/0.97  thf('218', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('219', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('220', plain,
% 0.76/0.97      (((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 0.76/0.97         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/0.97      inference('demod', [status(thm)], ['216', '217', '218', '219'])).
% 0.76/0.97  thf('221', plain,
% 0.76/0.97      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.76/0.97        | ~ (v1_relat_1 @ sk_C)
% 0.76/0.97        | ~ (v1_funct_1 @ sk_C)
% 0.76/0.97        | ~ (v2_funct_1 @ sk_C))),
% 0.76/0.97      inference('sup+', [status(thm)], ['202', '220'])).
% 0.76/0.97  thf('222', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.97      inference('sup-', [status(thm)], ['94', '95'])).
% 0.76/0.97  thf('223', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('224', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('225', plain,
% 0.76/0.97      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/0.97      inference('demod', [status(thm)], ['221', '222', '223', '224'])).
% 0.76/0.97  thf('226', plain,
% 0.76/0.97      (((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.76/0.97      inference('demod', [status(thm)], ['201', '225'])).
% 0.76/0.97  thf('227', plain,
% 0.76/0.97      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/0.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.76/0.97      inference('simplify', [status(thm)], ['90'])).
% 0.76/0.97  thf('228', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('229', plain,
% 0.76/0.97      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.76/0.97         (~ (v2_funct_1 @ X48)
% 0.76/0.97          | ((k2_relset_1 @ X50 @ X49 @ X48) != (X49))
% 0.76/0.97          | (v1_funct_2 @ (k2_funct_1 @ X48) @ X49 @ X50)
% 0.76/0.97          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 0.76/0.97          | ~ (v1_funct_2 @ X48 @ X50 @ X49)
% 0.76/0.97          | ~ (v1_funct_1 @ X48))),
% 0.76/0.97      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.76/0.97  thf('230', plain,
% 0.76/0.97      ((~ (v1_funct_1 @ sk_C)
% 0.76/0.97        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.76/0.97        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.76/0.97        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.76/0.97        | ~ (v2_funct_1 @ sk_C))),
% 0.76/0.97      inference('sup-', [status(thm)], ['228', '229'])).
% 0.76/0.97  thf('231', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('232', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('233', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('234', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('235', plain,
% 0.76/0.97      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.76/0.97      inference('demod', [status(thm)], ['230', '231', '232', '233', '234'])).
% 0.76/0.97  thf('236', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.76/0.97      inference('simplify', [status(thm)], ['235'])).
% 0.76/0.97  thf('237', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.76/0.97      inference('simplify', [status(thm)], ['81'])).
% 0.76/0.97  thf('238', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.76/0.97      inference('demod', [status(thm)],
% 0.76/0.97                ['197', '198', '226', '227', '236', '237'])).
% 0.76/0.97  thf('239', plain,
% 0.76/0.97      ((((sk_A) != (sk_A))
% 0.76/0.97        | ((k5_relat_1 @ sk_D @ sk_C) != (k6_relat_1 @ sk_B)))),
% 0.76/0.97      inference('demod', [status(thm)], ['189', '238'])).
% 0.76/0.97  thf('240', plain, (((k5_relat_1 @ sk_D @ sk_C) != (k6_relat_1 @ sk_B))),
% 0.76/0.97      inference('simplify', [status(thm)], ['239'])).
% 0.76/0.97  thf('241', plain, ($false),
% 0.76/0.97      inference('simplify_reflect-', [status(thm)], ['175', '240'])).
% 0.76/0.97  
% 0.76/0.97  % SZS output end Refutation
% 0.76/0.97  
% 0.76/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
