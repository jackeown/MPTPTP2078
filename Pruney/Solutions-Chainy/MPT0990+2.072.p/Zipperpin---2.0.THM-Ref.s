%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qooLMZOxSj

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:06 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  227 (1115 expanded)
%              Number of leaves         :   49 ( 353 expanded)
%              Depth                    :   29
%              Number of atoms          : 2194 (28226 expanded)
%              Number of equality atoms :  165 (1862 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

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

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ X51 @ ( k2_funct_1 @ X51 ) )
        = ( k6_partfun1 @ X52 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ X51 @ ( k2_funct_1 @ X51 ) )
        = ( k6_relat_1 @ X52 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','7','8','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('28',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('29',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_relset_1 @ X38 @ X38 @ ( k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40 ) @ ( k6_partfun1 @ X38 ) )
      | ( ( k2_relset_1 @ X39 @ X38 @ X40 )
        = X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('34',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('35',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_relset_1 @ X38 @ X38 @ ( k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40 ) @ ( k6_relat_1 @ X38 ) )
      | ( ( k2_relset_1 @ X39 @ X38 @ X40 )
        = X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('50',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','49'])).

thf('51',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

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
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( zip_tseitin_0 @ X45 @ X48 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X49 @ X46 @ X46 @ X47 @ X48 @ X45 ) )
      | ( zip_tseitin_1 @ X47 @ X46 )
      | ( ( k2_relset_1 @ X49 @ X46 @ X48 )
       != X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
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
    ! [X43: $i,X44: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X43 @ X44 ) ) ),
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
    ! [X41: $i,X42: $i] :
      ( ( v2_funct_1 @ X42 )
      | ~ ( zip_tseitin_0 @ X42 @ X41 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
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
    inference(demod,[status(thm)],['27','30'])).

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
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k2_funct_1 @ X11 ) )
      | ( ( k5_relat_1 @ X10 @ X11 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
      | ( ( k2_relat_1 @ X10 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('87',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('88',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('92',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['85','88','89','94','95','98'])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('101',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('104',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('105',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k10_relat_1 @ X8 @ X9 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X8 ) @ X9 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('106',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('107',plain,
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

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('109',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('110',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('111',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('112',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['86','87'])).

thf('113',plain,
    ( ( sk_B
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_B
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['86','87'])).

thf('116',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( sk_B
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_A ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ( sk_B
      = ( k10_relat_1 @ sk_D @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['105','117'])).

thf('119',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('120',plain,(
    ! [X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k2_relat_1 @ X2 ) )
        = ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('121',plain,
    ( ( ( k10_relat_1 @ sk_D @ sk_A )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['86','87'])).

thf('123',plain,
    ( ( k10_relat_1 @ sk_D @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['86','87'])).

thf('125',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('127',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['118','123','124','125','126'])).

thf('128',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['104','127'])).

thf('129',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['73','129'])).

thf('131',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k2_funct_1 @ X11 ) )
      | ( ( k5_relat_1 @ X10 @ X11 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
      | ( ( k2_relat_1 @ X10 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('132',plain,
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
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['92','93'])).

thf('134',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['96','97'])).

thf('135',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('138',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k10_relat_1 @ X8 @ X9 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X8 ) @ X9 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('139',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('140',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ X51 @ ( k2_funct_1 @ X51 ) )
        = ( k6_relat_1 @ X52 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('142',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['142','143','144','145','146'])).

thf('148',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('152',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('154',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['92','93'])).

thf('155',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['96','97'])).

thf('156',plain,
    ( ( sk_A
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['152','153','154','155'])).

thf('157',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_A
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['139','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['96','97'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( sk_A
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ( sk_A
      = ( k10_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['138','160'])).

thf('162',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['92','93'])).

thf('163',plain,(
    ! [X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k2_relat_1 @ X2 ) )
        = ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('164',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['96','97'])).

thf('166',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['96','97'])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['161','166','167','168','169'])).

thf('171',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['86','87'])).

thf('173',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['132','133','134','135','136','137','170','171','172'])).

thf('174',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['174','175'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qooLMZOxSj
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:59:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.80/2.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.80/2.08  % Solved by: fo/fo7.sh
% 1.80/2.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.80/2.08  % done 1216 iterations in 1.611s
% 1.80/2.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.80/2.08  % SZS output start Refutation
% 1.80/2.08  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.80/2.08  thf(sk_B_type, type, sk_B: $i).
% 1.80/2.08  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.80/2.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.80/2.08  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.80/2.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.80/2.08  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.80/2.08  thf(sk_D_type, type, sk_D: $i).
% 1.80/2.08  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.80/2.08  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.80/2.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.80/2.08  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.80/2.08  thf(sk_C_type, type, sk_C: $i).
% 1.80/2.08  thf(sk_A_type, type, sk_A: $i).
% 1.80/2.08  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.80/2.08  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.80/2.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.80/2.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.80/2.08  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.80/2.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.80/2.08  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.80/2.08  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.80/2.08  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.80/2.08  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.80/2.08  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.80/2.08  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.80/2.08  thf(t36_funct_2, conjecture,
% 1.80/2.08    (![A:$i,B:$i,C:$i]:
% 1.80/2.08     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.80/2.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.80/2.08       ( ![D:$i]:
% 1.80/2.08         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.80/2.08             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.80/2.08           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.80/2.08               ( r2_relset_1 @
% 1.80/2.08                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.80/2.08                 ( k6_partfun1 @ A ) ) & 
% 1.80/2.08               ( v2_funct_1 @ C ) ) =>
% 1.80/2.08             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.80/2.08               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.80/2.08  thf(zf_stmt_0, negated_conjecture,
% 1.80/2.08    (~( ![A:$i,B:$i,C:$i]:
% 1.80/2.08        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.80/2.08            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.80/2.08          ( ![D:$i]:
% 1.80/2.08            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.80/2.08                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.80/2.08              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.80/2.08                  ( r2_relset_1 @
% 1.80/2.08                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.80/2.08                    ( k6_partfun1 @ A ) ) & 
% 1.80/2.08                  ( v2_funct_1 @ C ) ) =>
% 1.80/2.08                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.80/2.08                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.80/2.08    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.80/2.08  thf('0', plain,
% 1.80/2.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf(t35_funct_2, axiom,
% 1.80/2.08    (![A:$i,B:$i,C:$i]:
% 1.80/2.08     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.80/2.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.80/2.08       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.80/2.08         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.80/2.08           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.80/2.08             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.80/2.08  thf('1', plain,
% 1.80/2.08      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.80/2.08         (((X50) = (k1_xboole_0))
% 1.80/2.08          | ~ (v1_funct_1 @ X51)
% 1.80/2.08          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.80/2.08          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.80/2.08          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_partfun1 @ X52))
% 1.80/2.08          | ~ (v2_funct_1 @ X51)
% 1.80/2.08          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.80/2.08      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.80/2.08  thf(redefinition_k6_partfun1, axiom,
% 1.80/2.08    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.80/2.08  thf('2', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.80/2.08      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.80/2.08  thf('3', plain,
% 1.80/2.08      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.80/2.08         (((X50) = (k1_xboole_0))
% 1.80/2.08          | ~ (v1_funct_1 @ X51)
% 1.80/2.08          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.80/2.08          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.80/2.08          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_relat_1 @ X52))
% 1.80/2.08          | ~ (v2_funct_1 @ X51)
% 1.80/2.08          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.80/2.08      inference('demod', [status(thm)], ['1', '2'])).
% 1.80/2.08  thf('4', plain,
% 1.80/2.08      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.80/2.08        | ~ (v2_funct_1 @ sk_D)
% 1.80/2.08        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.80/2.08        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.80/2.08        | ~ (v1_funct_1 @ sk_D)
% 1.80/2.08        | ((sk_A) = (k1_xboole_0)))),
% 1.80/2.08      inference('sup-', [status(thm)], ['0', '3'])).
% 1.80/2.08  thf('5', plain,
% 1.80/2.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf(redefinition_k2_relset_1, axiom,
% 1.80/2.08    (![A:$i,B:$i,C:$i]:
% 1.80/2.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.80/2.08       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.80/2.08  thf('6', plain,
% 1.80/2.08      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.80/2.08         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.80/2.08          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.80/2.08      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.80/2.08  thf('7', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.80/2.08      inference('sup-', [status(thm)], ['5', '6'])).
% 1.80/2.08  thf('8', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('10', plain,
% 1.80/2.08      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.80/2.08        | ~ (v2_funct_1 @ sk_D)
% 1.80/2.08        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.80/2.08        | ((sk_A) = (k1_xboole_0)))),
% 1.80/2.08      inference('demod', [status(thm)], ['4', '7', '8', '9'])).
% 1.80/2.08  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('12', plain,
% 1.80/2.08      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.80/2.08        | ~ (v2_funct_1 @ sk_D)
% 1.80/2.08        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 1.80/2.08      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 1.80/2.08  thf('13', plain,
% 1.80/2.08      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.80/2.08        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.80/2.08        (k6_partfun1 @ sk_A))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('14', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.80/2.08      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.80/2.08  thf('15', plain,
% 1.80/2.08      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.80/2.08        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.80/2.08        (k6_relat_1 @ sk_A))),
% 1.80/2.08      inference('demod', [status(thm)], ['13', '14'])).
% 1.80/2.08  thf('16', plain,
% 1.80/2.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('17', plain,
% 1.80/2.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf(dt_k1_partfun1, axiom,
% 1.80/2.08    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.80/2.08     ( ( ( v1_funct_1 @ E ) & 
% 1.80/2.08         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.80/2.08         ( v1_funct_1 @ F ) & 
% 1.80/2.08         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.80/2.08       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.80/2.08         ( m1_subset_1 @
% 1.80/2.08           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.80/2.08           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.80/2.08  thf('18', plain,
% 1.80/2.08      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.80/2.08         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.80/2.08          | ~ (v1_funct_1 @ X22)
% 1.80/2.08          | ~ (v1_funct_1 @ X25)
% 1.80/2.08          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.80/2.08          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 1.80/2.08             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 1.80/2.08      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.80/2.08  thf('19', plain,
% 1.80/2.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/2.08         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.80/2.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.80/2.08          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.80/2.08          | ~ (v1_funct_1 @ X1)
% 1.80/2.08          | ~ (v1_funct_1 @ sk_C))),
% 1.80/2.08      inference('sup-', [status(thm)], ['17', '18'])).
% 1.80/2.08  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('21', plain,
% 1.80/2.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/2.08         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.80/2.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.80/2.08          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.80/2.08          | ~ (v1_funct_1 @ X1))),
% 1.80/2.08      inference('demod', [status(thm)], ['19', '20'])).
% 1.80/2.08  thf('22', plain,
% 1.80/2.08      ((~ (v1_funct_1 @ sk_D)
% 1.80/2.08        | (m1_subset_1 @ 
% 1.80/2.08           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.80/2.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.80/2.08      inference('sup-', [status(thm)], ['16', '21'])).
% 1.80/2.08  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('24', plain,
% 1.80/2.08      ((m1_subset_1 @ 
% 1.80/2.08        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.80/2.08        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.80/2.08      inference('demod', [status(thm)], ['22', '23'])).
% 1.80/2.08  thf(redefinition_r2_relset_1, axiom,
% 1.80/2.08    (![A:$i,B:$i,C:$i,D:$i]:
% 1.80/2.08     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.80/2.08         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.80/2.08       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.80/2.08  thf('25', plain,
% 1.80/2.08      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.80/2.08         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.80/2.08          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.80/2.08          | ((X18) = (X21))
% 1.80/2.08          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 1.80/2.08      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.80/2.08  thf('26', plain,
% 1.80/2.08      (![X0 : $i]:
% 1.80/2.08         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.80/2.08             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.80/2.08          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.80/2.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.80/2.08      inference('sup-', [status(thm)], ['24', '25'])).
% 1.80/2.08  thf('27', plain,
% 1.80/2.08      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.80/2.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.80/2.08        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.80/2.08            = (k6_relat_1 @ sk_A)))),
% 1.80/2.08      inference('sup-', [status(thm)], ['15', '26'])).
% 1.80/2.08  thf(dt_k6_partfun1, axiom,
% 1.80/2.08    (![A:$i]:
% 1.80/2.08     ( ( m1_subset_1 @
% 1.80/2.08         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.80/2.08       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.80/2.08  thf('28', plain,
% 1.80/2.08      (![X29 : $i]:
% 1.80/2.08         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 1.80/2.08          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 1.80/2.08      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.80/2.08  thf('29', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.80/2.08      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.80/2.08  thf('30', plain,
% 1.80/2.08      (![X29 : $i]:
% 1.80/2.08         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 1.80/2.08          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 1.80/2.08      inference('demod', [status(thm)], ['28', '29'])).
% 1.80/2.08  thf('31', plain,
% 1.80/2.08      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.80/2.08         = (k6_relat_1 @ sk_A))),
% 1.80/2.08      inference('demod', [status(thm)], ['27', '30'])).
% 1.80/2.08  thf('32', plain,
% 1.80/2.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf(t24_funct_2, axiom,
% 1.80/2.08    (![A:$i,B:$i,C:$i]:
% 1.80/2.08     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.80/2.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.80/2.08       ( ![D:$i]:
% 1.80/2.08         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.80/2.08             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.80/2.08           ( ( r2_relset_1 @
% 1.80/2.08               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.80/2.08               ( k6_partfun1 @ B ) ) =>
% 1.80/2.08             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.80/2.08  thf('33', plain,
% 1.80/2.08      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.80/2.08         (~ (v1_funct_1 @ X37)
% 1.80/2.08          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 1.80/2.08          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.80/2.08          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 1.80/2.08               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 1.80/2.08               (k6_partfun1 @ X38))
% 1.80/2.08          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 1.80/2.08          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 1.80/2.08          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 1.80/2.08          | ~ (v1_funct_1 @ X40))),
% 1.80/2.08      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.80/2.08  thf('34', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.80/2.08      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.80/2.08  thf('35', plain,
% 1.80/2.08      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.80/2.08         (~ (v1_funct_1 @ X37)
% 1.80/2.08          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 1.80/2.08          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.80/2.08          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 1.80/2.08               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 1.80/2.08               (k6_relat_1 @ X38))
% 1.80/2.08          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 1.80/2.08          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 1.80/2.08          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 1.80/2.08          | ~ (v1_funct_1 @ X40))),
% 1.80/2.08      inference('demod', [status(thm)], ['33', '34'])).
% 1.80/2.08  thf('36', plain,
% 1.80/2.08      (![X0 : $i]:
% 1.80/2.08         (~ (v1_funct_1 @ X0)
% 1.80/2.08          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.80/2.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.80/2.08          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.80/2.08          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.80/2.08               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.80/2.08               (k6_relat_1 @ sk_A))
% 1.80/2.08          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.80/2.08          | ~ (v1_funct_1 @ sk_C))),
% 1.80/2.08      inference('sup-', [status(thm)], ['32', '35'])).
% 1.80/2.08  thf('37', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('39', plain,
% 1.80/2.08      (![X0 : $i]:
% 1.80/2.08         (~ (v1_funct_1 @ X0)
% 1.80/2.08          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.80/2.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.80/2.08          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.80/2.08          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.80/2.08               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.80/2.08               (k6_relat_1 @ sk_A)))),
% 1.80/2.08      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.80/2.08  thf('40', plain,
% 1.80/2.08      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.80/2.08           (k6_relat_1 @ sk_A))
% 1.80/2.08        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.80/2.08        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.80/2.08        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.80/2.08        | ~ (v1_funct_1 @ sk_D))),
% 1.80/2.08      inference('sup-', [status(thm)], ['31', '39'])).
% 1.80/2.08  thf('41', plain,
% 1.80/2.08      (![X29 : $i]:
% 1.80/2.08         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 1.80/2.08          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 1.80/2.08      inference('demod', [status(thm)], ['28', '29'])).
% 1.80/2.08  thf('42', plain,
% 1.80/2.08      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.80/2.08         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.80/2.08          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.80/2.08          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 1.80/2.08          | ((X18) != (X21)))),
% 1.80/2.08      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.80/2.08  thf('43', plain,
% 1.80/2.08      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.80/2.08         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 1.80/2.08          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.80/2.08      inference('simplify', [status(thm)], ['42'])).
% 1.80/2.08  thf('44', plain,
% 1.80/2.08      (![X0 : $i]:
% 1.80/2.08         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.80/2.08      inference('sup-', [status(thm)], ['41', '43'])).
% 1.80/2.08  thf('45', plain,
% 1.80/2.08      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.80/2.08      inference('sup-', [status(thm)], ['5', '6'])).
% 1.80/2.08  thf('46', plain,
% 1.80/2.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('47', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('49', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.80/2.08      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 1.80/2.08  thf('50', plain,
% 1.80/2.08      ((((sk_A) != (sk_A))
% 1.80/2.08        | ~ (v2_funct_1 @ sk_D)
% 1.80/2.08        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 1.80/2.08      inference('demod', [status(thm)], ['12', '49'])).
% 1.80/2.08  thf('51', plain,
% 1.80/2.08      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.80/2.08        | ~ (v2_funct_1 @ sk_D))),
% 1.80/2.08      inference('simplify', [status(thm)], ['50'])).
% 1.80/2.08  thf('52', plain,
% 1.80/2.08      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.80/2.08         = (k6_relat_1 @ sk_A))),
% 1.80/2.08      inference('demod', [status(thm)], ['27', '30'])).
% 1.80/2.08  thf('53', plain,
% 1.80/2.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf(t30_funct_2, axiom,
% 1.80/2.08    (![A:$i,B:$i,C:$i,D:$i]:
% 1.80/2.08     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.80/2.08         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.80/2.08       ( ![E:$i]:
% 1.80/2.08         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.80/2.08             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.80/2.08           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.80/2.08               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.80/2.08             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.80/2.08               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.80/2.08  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.80/2.08  thf(zf_stmt_2, axiom,
% 1.80/2.08    (![C:$i,B:$i]:
% 1.80/2.08     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.80/2.08       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.80/2.08  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.80/2.08  thf(zf_stmt_4, axiom,
% 1.80/2.08    (![E:$i,D:$i]:
% 1.80/2.08     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.80/2.08  thf(zf_stmt_5, axiom,
% 1.80/2.08    (![A:$i,B:$i,C:$i,D:$i]:
% 1.80/2.08     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.80/2.08         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.80/2.08       ( ![E:$i]:
% 1.80/2.08         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.80/2.08             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.80/2.08           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.80/2.08               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.80/2.08             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.80/2.08  thf('54', plain,
% 1.80/2.08      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.80/2.08         (~ (v1_funct_1 @ X45)
% 1.80/2.08          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 1.80/2.08          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 1.80/2.08          | (zip_tseitin_0 @ X45 @ X48)
% 1.80/2.08          | ~ (v2_funct_1 @ (k1_partfun1 @ X49 @ X46 @ X46 @ X47 @ X48 @ X45))
% 1.80/2.08          | (zip_tseitin_1 @ X47 @ X46)
% 1.80/2.08          | ((k2_relset_1 @ X49 @ X46 @ X48) != (X46))
% 1.80/2.08          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X46)))
% 1.80/2.08          | ~ (v1_funct_2 @ X48 @ X49 @ X46)
% 1.80/2.08          | ~ (v1_funct_1 @ X48))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.80/2.08  thf('55', plain,
% 1.80/2.08      (![X0 : $i, X1 : $i]:
% 1.80/2.08         (~ (v1_funct_1 @ X0)
% 1.80/2.08          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.80/2.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.80/2.08          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.80/2.08          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.80/2.08          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.80/2.08          | (zip_tseitin_0 @ sk_D @ X0)
% 1.80/2.08          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.80/2.08          | ~ (v1_funct_1 @ sk_D))),
% 1.80/2.08      inference('sup-', [status(thm)], ['53', '54'])).
% 1.80/2.08  thf('56', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('58', plain,
% 1.80/2.08      (![X0 : $i, X1 : $i]:
% 1.80/2.08         (~ (v1_funct_1 @ X0)
% 1.80/2.08          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.80/2.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.80/2.08          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.80/2.08          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.80/2.08          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.80/2.08          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.80/2.08      inference('demod', [status(thm)], ['55', '56', '57'])).
% 1.80/2.08  thf('59', plain,
% 1.80/2.08      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.80/2.08        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.80/2.08        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.80/2.08        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.80/2.08        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.80/2.08        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.80/2.08        | ~ (v1_funct_1 @ sk_C))),
% 1.80/2.08      inference('sup-', [status(thm)], ['52', '58'])).
% 1.80/2.08  thf(fc4_funct_1, axiom,
% 1.80/2.08    (![A:$i]:
% 1.80/2.08     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.80/2.08       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.80/2.08  thf('60', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 1.80/2.08      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.80/2.08  thf('61', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('62', plain,
% 1.80/2.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('63', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('65', plain,
% 1.80/2.08      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.80/2.08        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.80/2.08        | ((sk_B) != (sk_B)))),
% 1.80/2.08      inference('demod', [status(thm)], ['59', '60', '61', '62', '63', '64'])).
% 1.80/2.08  thf('66', plain,
% 1.80/2.08      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.80/2.08      inference('simplify', [status(thm)], ['65'])).
% 1.80/2.08  thf('67', plain,
% 1.80/2.08      (![X43 : $i, X44 : $i]:
% 1.80/2.08         (((X43) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X43 @ X44))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.80/2.08  thf('68', plain,
% 1.80/2.08      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.80/2.08      inference('sup-', [status(thm)], ['66', '67'])).
% 1.80/2.08  thf('69', plain, (((sk_A) != (k1_xboole_0))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('70', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.80/2.08      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 1.80/2.08  thf('71', plain,
% 1.80/2.08      (![X41 : $i, X42 : $i]:
% 1.80/2.08         ((v2_funct_1 @ X42) | ~ (zip_tseitin_0 @ X42 @ X41))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.80/2.08  thf('72', plain, ((v2_funct_1 @ sk_D)),
% 1.80/2.08      inference('sup-', [status(thm)], ['70', '71'])).
% 1.80/2.08  thf('73', plain,
% 1.80/2.08      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 1.80/2.08      inference('demod', [status(thm)], ['51', '72'])).
% 1.80/2.08  thf('74', plain,
% 1.80/2.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('75', plain,
% 1.80/2.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf(redefinition_k1_partfun1, axiom,
% 1.80/2.08    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.80/2.08     ( ( ( v1_funct_1 @ E ) & 
% 1.80/2.08         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.80/2.08         ( v1_funct_1 @ F ) & 
% 1.80/2.08         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.80/2.08       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.80/2.08  thf('76', plain,
% 1.80/2.08      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.80/2.08         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.80/2.08          | ~ (v1_funct_1 @ X30)
% 1.80/2.08          | ~ (v1_funct_1 @ X33)
% 1.80/2.08          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.80/2.08          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 1.80/2.08              = (k5_relat_1 @ X30 @ X33)))),
% 1.80/2.08      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.80/2.08  thf('77', plain,
% 1.80/2.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/2.08         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.80/2.08            = (k5_relat_1 @ sk_C @ X0))
% 1.80/2.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.80/2.08          | ~ (v1_funct_1 @ X0)
% 1.80/2.08          | ~ (v1_funct_1 @ sk_C))),
% 1.80/2.08      inference('sup-', [status(thm)], ['75', '76'])).
% 1.80/2.08  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('79', plain,
% 1.80/2.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/2.08         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.80/2.08            = (k5_relat_1 @ sk_C @ X0))
% 1.80/2.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.80/2.08          | ~ (v1_funct_1 @ X0))),
% 1.80/2.08      inference('demod', [status(thm)], ['77', '78'])).
% 1.80/2.08  thf('80', plain,
% 1.80/2.08      ((~ (v1_funct_1 @ sk_D)
% 1.80/2.08        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.80/2.08            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.80/2.08      inference('sup-', [status(thm)], ['74', '79'])).
% 1.80/2.08  thf('81', plain, ((v1_funct_1 @ sk_D)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('82', plain,
% 1.80/2.08      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.80/2.08         = (k6_relat_1 @ sk_A))),
% 1.80/2.08      inference('demod', [status(thm)], ['27', '30'])).
% 1.80/2.08  thf('83', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.80/2.08      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.80/2.08  thf(t64_funct_1, axiom,
% 1.80/2.08    (![A:$i]:
% 1.80/2.08     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.80/2.08       ( ![B:$i]:
% 1.80/2.08         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.80/2.08           ( ( ( v2_funct_1 @ A ) & 
% 1.80/2.08               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.80/2.08               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.80/2.08             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.80/2.08  thf('84', plain,
% 1.80/2.08      (![X10 : $i, X11 : $i]:
% 1.80/2.08         (~ (v1_relat_1 @ X10)
% 1.80/2.08          | ~ (v1_funct_1 @ X10)
% 1.80/2.08          | ((X10) = (k2_funct_1 @ X11))
% 1.80/2.08          | ((k5_relat_1 @ X10 @ X11) != (k6_relat_1 @ (k2_relat_1 @ X11)))
% 1.80/2.08          | ((k2_relat_1 @ X10) != (k1_relat_1 @ X11))
% 1.80/2.08          | ~ (v2_funct_1 @ X11)
% 1.80/2.08          | ~ (v1_funct_1 @ X11)
% 1.80/2.08          | ~ (v1_relat_1 @ X11))),
% 1.80/2.08      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.80/2.08  thf('85', plain,
% 1.80/2.08      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 1.80/2.08        | ~ (v1_relat_1 @ sk_D)
% 1.80/2.08        | ~ (v1_funct_1 @ sk_D)
% 1.80/2.08        | ~ (v2_funct_1 @ sk_D)
% 1.80/2.08        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.80/2.08        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.80/2.08        | ~ (v1_funct_1 @ sk_C)
% 1.80/2.08        | ~ (v1_relat_1 @ sk_C))),
% 1.80/2.08      inference('sup-', [status(thm)], ['83', '84'])).
% 1.80/2.08  thf('86', plain,
% 1.80/2.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf(cc1_relset_1, axiom,
% 1.80/2.08    (![A:$i,B:$i,C:$i]:
% 1.80/2.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.80/2.08       ( v1_relat_1 @ C ) ))).
% 1.80/2.08  thf('87', plain,
% 1.80/2.08      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.80/2.08         ((v1_relat_1 @ X12)
% 1.80/2.08          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.80/2.08      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.80/2.08  thf('88', plain, ((v1_relat_1 @ sk_D)),
% 1.80/2.08      inference('sup-', [status(thm)], ['86', '87'])).
% 1.80/2.08  thf('89', plain, ((v1_funct_1 @ sk_D)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('90', plain,
% 1.80/2.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('91', plain,
% 1.80/2.08      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.80/2.08         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.80/2.08          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.80/2.08      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.80/2.08  thf('92', plain,
% 1.80/2.08      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.80/2.08      inference('sup-', [status(thm)], ['90', '91'])).
% 1.80/2.08  thf('93', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('94', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.80/2.08      inference('sup+', [status(thm)], ['92', '93'])).
% 1.80/2.08  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('96', plain,
% 1.80/2.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('97', plain,
% 1.80/2.08      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.80/2.08         ((v1_relat_1 @ X12)
% 1.80/2.08          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.80/2.08      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.80/2.08  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 1.80/2.08      inference('sup-', [status(thm)], ['96', '97'])).
% 1.80/2.08  thf('99', plain,
% 1.80/2.08      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 1.80/2.08        | ~ (v2_funct_1 @ sk_D)
% 1.80/2.08        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.80/2.08        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.80/2.08      inference('demod', [status(thm)], ['85', '88', '89', '94', '95', '98'])).
% 1.80/2.08  thf('100', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.80/2.08      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 1.80/2.08  thf('101', plain,
% 1.80/2.08      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 1.80/2.08        | ~ (v2_funct_1 @ sk_D)
% 1.80/2.08        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.80/2.08        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.80/2.08      inference('demod', [status(thm)], ['99', '100'])).
% 1.80/2.08  thf('102', plain,
% 1.80/2.08      ((((sk_C) = (k2_funct_1 @ sk_D))
% 1.80/2.08        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.80/2.08        | ~ (v2_funct_1 @ sk_D))),
% 1.80/2.08      inference('simplify', [status(thm)], ['101'])).
% 1.80/2.08  thf('103', plain, ((v2_funct_1 @ sk_D)),
% 1.80/2.08      inference('sup-', [status(thm)], ['70', '71'])).
% 1.80/2.08  thf('104', plain,
% 1.80/2.08      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 1.80/2.08      inference('demod', [status(thm)], ['102', '103'])).
% 1.80/2.08  thf(t155_funct_1, axiom,
% 1.80/2.08    (![A:$i,B:$i]:
% 1.80/2.08     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.80/2.08       ( ( v2_funct_1 @ B ) =>
% 1.80/2.08         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 1.80/2.08  thf('105', plain,
% 1.80/2.08      (![X8 : $i, X9 : $i]:
% 1.80/2.08         (~ (v2_funct_1 @ X8)
% 1.80/2.08          | ((k10_relat_1 @ X8 @ X9) = (k9_relat_1 @ (k2_funct_1 @ X8) @ X9))
% 1.80/2.08          | ~ (v1_funct_1 @ X8)
% 1.80/2.08          | ~ (v1_relat_1 @ X8))),
% 1.80/2.08      inference('cnf', [status(esa)], [t155_funct_1])).
% 1.80/2.08  thf(dt_k2_funct_1, axiom,
% 1.80/2.08    (![A:$i]:
% 1.80/2.08     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.80/2.08       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.80/2.08         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.80/2.08  thf('106', plain,
% 1.80/2.08      (![X5 : $i]:
% 1.80/2.08         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 1.80/2.08          | ~ (v1_funct_1 @ X5)
% 1.80/2.08          | ~ (v1_relat_1 @ X5))),
% 1.80/2.08      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.80/2.08  thf('107', plain,
% 1.80/2.08      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 1.80/2.08      inference('demod', [status(thm)], ['51', '72'])).
% 1.80/2.08  thf(t160_relat_1, axiom,
% 1.80/2.08    (![A:$i]:
% 1.80/2.08     ( ( v1_relat_1 @ A ) =>
% 1.80/2.08       ( ![B:$i]:
% 1.80/2.08         ( ( v1_relat_1 @ B ) =>
% 1.80/2.08           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.80/2.08             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.80/2.08  thf('108', plain,
% 1.80/2.08      (![X0 : $i, X1 : $i]:
% 1.80/2.08         (~ (v1_relat_1 @ X0)
% 1.80/2.08          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.80/2.08              = (k9_relat_1 @ X0 @ (k2_relat_1 @ X1)))
% 1.80/2.08          | ~ (v1_relat_1 @ X1))),
% 1.80/2.08      inference('cnf', [status(esa)], [t160_relat_1])).
% 1.80/2.08  thf('109', plain,
% 1.80/2.08      ((((k2_relat_1 @ (k6_relat_1 @ sk_B))
% 1.80/2.08          = (k9_relat_1 @ (k2_funct_1 @ sk_D) @ (k2_relat_1 @ sk_D)))
% 1.80/2.08        | ~ (v1_relat_1 @ sk_D)
% 1.80/2.08        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 1.80/2.08      inference('sup+', [status(thm)], ['107', '108'])).
% 1.80/2.08  thf(t71_relat_1, axiom,
% 1.80/2.08    (![A:$i]:
% 1.80/2.08     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.80/2.08       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.80/2.08  thf('110', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 1.80/2.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.80/2.08  thf('111', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.80/2.08      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 1.80/2.08  thf('112', plain, ((v1_relat_1 @ sk_D)),
% 1.80/2.08      inference('sup-', [status(thm)], ['86', '87'])).
% 1.80/2.08  thf('113', plain,
% 1.80/2.08      ((((sk_B) = (k9_relat_1 @ (k2_funct_1 @ sk_D) @ sk_A))
% 1.80/2.08        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 1.80/2.08      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 1.80/2.08  thf('114', plain,
% 1.80/2.08      ((~ (v1_relat_1 @ sk_D)
% 1.80/2.08        | ~ (v1_funct_1 @ sk_D)
% 1.80/2.08        | ((sk_B) = (k9_relat_1 @ (k2_funct_1 @ sk_D) @ sk_A)))),
% 1.80/2.08      inference('sup-', [status(thm)], ['106', '113'])).
% 1.80/2.08  thf('115', plain, ((v1_relat_1 @ sk_D)),
% 1.80/2.08      inference('sup-', [status(thm)], ['86', '87'])).
% 1.80/2.08  thf('116', plain, ((v1_funct_1 @ sk_D)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('117', plain, (((sk_B) = (k9_relat_1 @ (k2_funct_1 @ sk_D) @ sk_A))),
% 1.80/2.08      inference('demod', [status(thm)], ['114', '115', '116'])).
% 1.80/2.08  thf('118', plain,
% 1.80/2.08      ((((sk_B) = (k10_relat_1 @ sk_D @ sk_A))
% 1.80/2.08        | ~ (v1_relat_1 @ sk_D)
% 1.80/2.08        | ~ (v1_funct_1 @ sk_D)
% 1.80/2.08        | ~ (v2_funct_1 @ sk_D))),
% 1.80/2.08      inference('sup+', [status(thm)], ['105', '117'])).
% 1.80/2.08  thf('119', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.80/2.08      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 1.80/2.08  thf(t169_relat_1, axiom,
% 1.80/2.08    (![A:$i]:
% 1.80/2.08     ( ( v1_relat_1 @ A ) =>
% 1.80/2.08       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.80/2.08  thf('120', plain,
% 1.80/2.08      (![X2 : $i]:
% 1.80/2.08         (((k10_relat_1 @ X2 @ (k2_relat_1 @ X2)) = (k1_relat_1 @ X2))
% 1.80/2.08          | ~ (v1_relat_1 @ X2))),
% 1.80/2.08      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.80/2.08  thf('121', plain,
% 1.80/2.08      ((((k10_relat_1 @ sk_D @ sk_A) = (k1_relat_1 @ sk_D))
% 1.80/2.08        | ~ (v1_relat_1 @ sk_D))),
% 1.80/2.08      inference('sup+', [status(thm)], ['119', '120'])).
% 1.80/2.08  thf('122', plain, ((v1_relat_1 @ sk_D)),
% 1.80/2.08      inference('sup-', [status(thm)], ['86', '87'])).
% 1.80/2.08  thf('123', plain, (((k10_relat_1 @ sk_D @ sk_A) = (k1_relat_1 @ sk_D))),
% 1.80/2.08      inference('demod', [status(thm)], ['121', '122'])).
% 1.80/2.08  thf('124', plain, ((v1_relat_1 @ sk_D)),
% 1.80/2.08      inference('sup-', [status(thm)], ['86', '87'])).
% 1.80/2.08  thf('125', plain, ((v1_funct_1 @ sk_D)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('126', plain, ((v2_funct_1 @ sk_D)),
% 1.80/2.08      inference('sup-', [status(thm)], ['70', '71'])).
% 1.80/2.08  thf('127', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.80/2.08      inference('demod', [status(thm)], ['118', '123', '124', '125', '126'])).
% 1.80/2.08  thf('128', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 1.80/2.08      inference('demod', [status(thm)], ['104', '127'])).
% 1.80/2.08  thf('129', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.80/2.08      inference('simplify', [status(thm)], ['128'])).
% 1.80/2.08  thf('130', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 1.80/2.08      inference('demod', [status(thm)], ['73', '129'])).
% 1.80/2.08  thf('131', plain,
% 1.80/2.08      (![X10 : $i, X11 : $i]:
% 1.80/2.08         (~ (v1_relat_1 @ X10)
% 1.80/2.08          | ~ (v1_funct_1 @ X10)
% 1.80/2.08          | ((X10) = (k2_funct_1 @ X11))
% 1.80/2.08          | ((k5_relat_1 @ X10 @ X11) != (k6_relat_1 @ (k2_relat_1 @ X11)))
% 1.80/2.08          | ((k2_relat_1 @ X10) != (k1_relat_1 @ X11))
% 1.80/2.08          | ~ (v2_funct_1 @ X11)
% 1.80/2.08          | ~ (v1_funct_1 @ X11)
% 1.80/2.08          | ~ (v1_relat_1 @ X11))),
% 1.80/2.08      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.80/2.08  thf('132', plain,
% 1.80/2.08      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 1.80/2.08        | ~ (v1_relat_1 @ sk_C)
% 1.80/2.08        | ~ (v1_funct_1 @ sk_C)
% 1.80/2.08        | ~ (v2_funct_1 @ sk_C)
% 1.80/2.08        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_C))
% 1.80/2.08        | ((sk_D) = (k2_funct_1 @ sk_C))
% 1.80/2.08        | ~ (v1_funct_1 @ sk_D)
% 1.80/2.08        | ~ (v1_relat_1 @ sk_D))),
% 1.80/2.08      inference('sup-', [status(thm)], ['130', '131'])).
% 1.80/2.08  thf('133', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.80/2.08      inference('sup+', [status(thm)], ['92', '93'])).
% 1.80/2.08  thf('134', plain, ((v1_relat_1 @ sk_C)),
% 1.80/2.08      inference('sup-', [status(thm)], ['96', '97'])).
% 1.80/2.08  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('136', plain, ((v2_funct_1 @ sk_C)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('137', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.80/2.08      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 1.80/2.08  thf('138', plain,
% 1.80/2.08      (![X8 : $i, X9 : $i]:
% 1.80/2.08         (~ (v2_funct_1 @ X8)
% 1.80/2.08          | ((k10_relat_1 @ X8 @ X9) = (k9_relat_1 @ (k2_funct_1 @ X8) @ X9))
% 1.80/2.08          | ~ (v1_funct_1 @ X8)
% 1.80/2.08          | ~ (v1_relat_1 @ X8))),
% 1.80/2.08      inference('cnf', [status(esa)], [t155_funct_1])).
% 1.80/2.08  thf('139', plain,
% 1.80/2.08      (![X5 : $i]:
% 1.80/2.08         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 1.80/2.08          | ~ (v1_funct_1 @ X5)
% 1.80/2.08          | ~ (v1_relat_1 @ X5))),
% 1.80/2.08      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.80/2.08  thf('140', plain,
% 1.80/2.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('141', plain,
% 1.80/2.08      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.80/2.08         (((X50) = (k1_xboole_0))
% 1.80/2.08          | ~ (v1_funct_1 @ X51)
% 1.80/2.08          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.80/2.08          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.80/2.08          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_relat_1 @ X52))
% 1.80/2.08          | ~ (v2_funct_1 @ X51)
% 1.80/2.08          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.80/2.08      inference('demod', [status(thm)], ['1', '2'])).
% 1.80/2.08  thf('142', plain,
% 1.80/2.08      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.80/2.08        | ~ (v2_funct_1 @ sk_C)
% 1.80/2.08        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.80/2.08        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.80/2.08        | ~ (v1_funct_1 @ sk_C)
% 1.80/2.08        | ((sk_B) = (k1_xboole_0)))),
% 1.80/2.08      inference('sup-', [status(thm)], ['140', '141'])).
% 1.80/2.08  thf('143', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('145', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('147', plain,
% 1.80/2.08      ((((sk_B) != (sk_B))
% 1.80/2.08        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.80/2.08        | ((sk_B) = (k1_xboole_0)))),
% 1.80/2.08      inference('demod', [status(thm)], ['142', '143', '144', '145', '146'])).
% 1.80/2.08  thf('148', plain,
% 1.80/2.08      ((((sk_B) = (k1_xboole_0))
% 1.80/2.08        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 1.80/2.08      inference('simplify', [status(thm)], ['147'])).
% 1.80/2.08  thf('149', plain, (((sk_B) != (k1_xboole_0))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('150', plain,
% 1.80/2.08      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 1.80/2.08      inference('simplify_reflect-', [status(thm)], ['148', '149'])).
% 1.80/2.08  thf('151', plain,
% 1.80/2.08      (![X0 : $i, X1 : $i]:
% 1.80/2.08         (~ (v1_relat_1 @ X0)
% 1.80/2.08          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.80/2.08              = (k9_relat_1 @ X0 @ (k2_relat_1 @ X1)))
% 1.80/2.08          | ~ (v1_relat_1 @ X1))),
% 1.80/2.08      inference('cnf', [status(esa)], [t160_relat_1])).
% 1.80/2.08  thf('152', plain,
% 1.80/2.08      ((((k2_relat_1 @ (k6_relat_1 @ sk_A))
% 1.80/2.08          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))
% 1.80/2.08        | ~ (v1_relat_1 @ sk_C)
% 1.80/2.08        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.80/2.08      inference('sup+', [status(thm)], ['150', '151'])).
% 1.80/2.08  thf('153', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 1.80/2.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.80/2.08  thf('154', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.80/2.08      inference('sup+', [status(thm)], ['92', '93'])).
% 1.80/2.08  thf('155', plain, ((v1_relat_1 @ sk_C)),
% 1.80/2.08      inference('sup-', [status(thm)], ['96', '97'])).
% 1.80/2.08  thf('156', plain,
% 1.80/2.08      ((((sk_A) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))
% 1.80/2.08        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.80/2.08      inference('demod', [status(thm)], ['152', '153', '154', '155'])).
% 1.80/2.08  thf('157', plain,
% 1.80/2.08      ((~ (v1_relat_1 @ sk_C)
% 1.80/2.08        | ~ (v1_funct_1 @ sk_C)
% 1.80/2.08        | ((sk_A) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)))),
% 1.80/2.08      inference('sup-', [status(thm)], ['139', '156'])).
% 1.80/2.08  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 1.80/2.08      inference('sup-', [status(thm)], ['96', '97'])).
% 1.80/2.08  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('160', plain, (((sk_A) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 1.80/2.08      inference('demod', [status(thm)], ['157', '158', '159'])).
% 1.80/2.08  thf('161', plain,
% 1.80/2.08      ((((sk_A) = (k10_relat_1 @ sk_C @ sk_B))
% 1.80/2.08        | ~ (v1_relat_1 @ sk_C)
% 1.80/2.08        | ~ (v1_funct_1 @ sk_C)
% 1.80/2.08        | ~ (v2_funct_1 @ sk_C))),
% 1.80/2.08      inference('sup+', [status(thm)], ['138', '160'])).
% 1.80/2.08  thf('162', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.80/2.08      inference('sup+', [status(thm)], ['92', '93'])).
% 1.80/2.08  thf('163', plain,
% 1.80/2.08      (![X2 : $i]:
% 1.80/2.08         (((k10_relat_1 @ X2 @ (k2_relat_1 @ X2)) = (k1_relat_1 @ X2))
% 1.80/2.08          | ~ (v1_relat_1 @ X2))),
% 1.80/2.08      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.80/2.08  thf('164', plain,
% 1.80/2.08      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 1.80/2.08        | ~ (v1_relat_1 @ sk_C))),
% 1.80/2.08      inference('sup+', [status(thm)], ['162', '163'])).
% 1.80/2.08  thf('165', plain, ((v1_relat_1 @ sk_C)),
% 1.80/2.08      inference('sup-', [status(thm)], ['96', '97'])).
% 1.80/2.08  thf('166', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 1.80/2.08      inference('demod', [status(thm)], ['164', '165'])).
% 1.80/2.08  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 1.80/2.08      inference('sup-', [status(thm)], ['96', '97'])).
% 1.80/2.08  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('169', plain, ((v2_funct_1 @ sk_C)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('170', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.80/2.08      inference('demod', [status(thm)], ['161', '166', '167', '168', '169'])).
% 1.80/2.08  thf('171', plain, ((v1_funct_1 @ sk_D)),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('172', plain, ((v1_relat_1 @ sk_D)),
% 1.80/2.08      inference('sup-', [status(thm)], ['86', '87'])).
% 1.80/2.08  thf('173', plain,
% 1.80/2.08      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 1.80/2.08        | ((sk_A) != (sk_A))
% 1.80/2.08        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.80/2.08      inference('demod', [status(thm)],
% 1.80/2.08                ['132', '133', '134', '135', '136', '137', '170', '171', '172'])).
% 1.80/2.08  thf('174', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.80/2.08      inference('simplify', [status(thm)], ['173'])).
% 1.80/2.08  thf('175', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.80/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.08  thf('176', plain, ($false),
% 1.80/2.08      inference('simplify_reflect-', [status(thm)], ['174', '175'])).
% 1.80/2.08  
% 1.80/2.08  % SZS output end Refutation
% 1.80/2.08  
% 1.93/2.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
