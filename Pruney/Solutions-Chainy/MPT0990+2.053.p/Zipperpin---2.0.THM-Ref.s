%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LIQKHvat3t

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:02 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 334 expanded)
%              Number of leaves         :   41 ( 117 expanded)
%              Depth                    :   15
%              Number of atoms          : 1406 (8586 expanded)
%              Number of equality atoms :   91 ( 604 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','9'])).

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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
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

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v2_funct_1 @ X37 )
      | ( ( k2_relset_1 @ X39 @ X38 @ X37 )
       != X38 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('37',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v2_funct_1 @ X37 )
      | ( ( k2_relset_1 @ X39 @ X38 @ X37 )
       != X38 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('40',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('49',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['45'])).

thf('51',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','46','51'])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['26','52'])).

thf('54',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('55',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('56',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('57',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('65',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('66',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','63','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('69',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','67','70','71','72'])).

thf('74',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','73'])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('75',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X1
        = ( k2_funct_1 @ X2 ) )
      | ( ( k5_relat_1 @ X2 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X2 ) ) )
      | ( ( k2_relat_1 @ X2 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('76',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('77',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X1
        = ( k2_funct_1 @ X2 ) )
      | ( ( k5_relat_1 @ X2 @ X1 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X2 ) ) )
      | ( ( k2_relat_1 @ X2 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','63','66'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('84',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('85',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('90',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('92',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('94',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('100',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['90','97','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('105',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_B != sk_B )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82','87','101','102','105'])).

thf('107',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['107','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LIQKHvat3t
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:04:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.77/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/0.98  % Solved by: fo/fo7.sh
% 0.77/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.98  % done 342 iterations in 0.521s
% 0.77/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/0.98  % SZS output start Refutation
% 0.77/0.98  thf(sk_D_type, type, sk_D: $i).
% 0.77/0.98  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.77/0.98  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.77/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.77/0.98  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.77/0.98  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.77/0.98  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.77/0.98  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.77/0.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.77/0.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.77/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.77/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.77/0.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.77/0.98  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.77/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.77/0.98  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.77/0.98  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.77/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.98  thf(sk_C_type, type, sk_C: $i).
% 0.77/0.98  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.77/0.98  thf(t36_funct_2, conjecture,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.77/0.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.77/0.98       ( ![D:$i]:
% 0.77/0.98         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.77/0.98             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.77/0.98           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.77/0.98               ( r2_relset_1 @
% 0.77/0.98                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.77/0.98                 ( k6_partfun1 @ A ) ) & 
% 0.77/0.98               ( v2_funct_1 @ C ) ) =>
% 0.77/0.98             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.77/0.98               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.77/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.98    (~( ![A:$i,B:$i,C:$i]:
% 0.77/0.98        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.77/0.98            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.77/0.98          ( ![D:$i]:
% 0.77/0.98            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.77/0.98                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.77/0.98              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.77/0.98                  ( r2_relset_1 @
% 0.77/0.98                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.77/0.98                    ( k6_partfun1 @ A ) ) & 
% 0.77/0.98                  ( v2_funct_1 @ C ) ) =>
% 0.77/0.98                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.77/0.98                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.77/0.98    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.77/0.98  thf('0', plain,
% 0.77/0.98      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/0.98        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.77/0.98        (k6_partfun1 @ sk_A))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('1', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('2', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf(redefinition_k1_partfun1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.77/0.98     ( ( ( v1_funct_1 @ E ) & 
% 0.77/0.98         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.77/0.98         ( v1_funct_1 @ F ) & 
% 0.77/0.98         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.77/0.98       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.77/0.98  thf('3', plain,
% 0.77/0.98      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.77/0.98         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.77/0.98          | ~ (v1_funct_1 @ X30)
% 0.77/0.98          | ~ (v1_funct_1 @ X33)
% 0.77/0.98          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.77/0.98          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 0.77/0.98              = (k5_relat_1 @ X30 @ X33)))),
% 0.77/0.98      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.77/0.98  thf('4', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.98         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.77/0.98            = (k5_relat_1 @ sk_C @ X0))
% 0.77/0.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.77/0.98          | ~ (v1_funct_1 @ X0)
% 0.77/0.98          | ~ (v1_funct_1 @ sk_C))),
% 0.77/0.98      inference('sup-', [status(thm)], ['2', '3'])).
% 0.77/0.98  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('6', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.98         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.77/0.98            = (k5_relat_1 @ sk_C @ X0))
% 0.77/0.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.77/0.98          | ~ (v1_funct_1 @ X0))),
% 0.77/0.98      inference('demod', [status(thm)], ['4', '5'])).
% 0.77/0.98  thf('7', plain,
% 0.77/0.98      ((~ (v1_funct_1 @ sk_D)
% 0.77/0.98        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.77/0.98            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.77/0.98      inference('sup-', [status(thm)], ['1', '6'])).
% 0.77/0.98  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('9', plain,
% 0.77/0.98      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.77/0.98         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.77/0.98      inference('demod', [status(thm)], ['7', '8'])).
% 0.77/0.98  thf('10', plain,
% 0.77/0.98      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.77/0.98        (k6_partfun1 @ sk_A))),
% 0.77/0.98      inference('demod', [status(thm)], ['0', '9'])).
% 0.77/0.98  thf('11', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('12', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf(dt_k1_partfun1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.77/0.98     ( ( ( v1_funct_1 @ E ) & 
% 0.77/0.98         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.77/0.98         ( v1_funct_1 @ F ) & 
% 0.77/0.98         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.77/0.98       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.77/0.98         ( m1_subset_1 @
% 0.77/0.98           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.77/0.98           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.77/0.98  thf('13', plain,
% 0.77/0.98      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.77/0.98         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.77/0.98          | ~ (v1_funct_1 @ X24)
% 0.77/0.98          | ~ (v1_funct_1 @ X27)
% 0.77/0.98          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.77/0.98          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 0.77/0.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 0.77/0.98      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.77/0.98  thf('14', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.98         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.77/0.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.77/0.98          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.77/0.98          | ~ (v1_funct_1 @ X1)
% 0.77/0.98          | ~ (v1_funct_1 @ sk_C))),
% 0.77/0.98      inference('sup-', [status(thm)], ['12', '13'])).
% 0.77/0.98  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('16', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.98         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.77/0.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.77/0.98          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.77/0.98          | ~ (v1_funct_1 @ X1))),
% 0.77/0.98      inference('demod', [status(thm)], ['14', '15'])).
% 0.77/0.98  thf('17', plain,
% 0.77/0.98      ((~ (v1_funct_1 @ sk_D)
% 0.77/0.98        | (m1_subset_1 @ 
% 0.77/0.98           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.77/0.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.77/0.98      inference('sup-', [status(thm)], ['11', '16'])).
% 0.77/0.98  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('19', plain,
% 0.77/0.98      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.77/0.98         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.77/0.98      inference('demod', [status(thm)], ['7', '8'])).
% 0.77/0.98  thf('20', plain,
% 0.77/0.98      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.77/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/0.98      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.77/0.98  thf(redefinition_r2_relset_1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.98     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.77/0.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.77/0.98       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.77/0.98  thf('21', plain,
% 0.77/0.98      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.77/0.98         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.77/0.98          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.77/0.98          | ((X12) = (X15))
% 0.77/0.98          | ~ (r2_relset_1 @ X13 @ X14 @ X12 @ X15))),
% 0.77/0.98      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.77/0.98  thf('22', plain,
% 0.77/0.98      (![X0 : $i]:
% 0.77/0.98         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.77/0.98          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.77/0.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.77/0.98      inference('sup-', [status(thm)], ['20', '21'])).
% 0.77/0.98  thf('23', plain,
% 0.77/0.98      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.77/0.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.77/0.98        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.77/0.98      inference('sup-', [status(thm)], ['10', '22'])).
% 0.77/0.98  thf(t61_funct_1, axiom,
% 0.77/0.98    (![A:$i]:
% 0.77/0.98     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.98       ( ( v2_funct_1 @ A ) =>
% 0.77/0.98         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.77/0.98             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.77/0.98           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.77/0.98             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.77/0.98  thf('24', plain,
% 0.77/0.98      (![X0 : $i]:
% 0.77/0.98         (~ (v2_funct_1 @ X0)
% 0.77/0.98          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.77/0.98              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.77/0.98          | ~ (v1_funct_1 @ X0)
% 0.77/0.98          | ~ (v1_relat_1 @ X0))),
% 0.77/0.98      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.77/0.98  thf(redefinition_k6_partfun1, axiom,
% 0.77/0.98    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.77/0.98  thf('25', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.77/0.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.77/0.98  thf('26', plain,
% 0.77/0.98      (![X0 : $i]:
% 0.77/0.98         (~ (v2_funct_1 @ X0)
% 0.77/0.98          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.77/0.98              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.77/0.98          | ~ (v1_funct_1 @ X0)
% 0.77/0.98          | ~ (v1_relat_1 @ X0))),
% 0.77/0.98      inference('demod', [status(thm)], ['24', '25'])).
% 0.77/0.98  thf('27', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf(t31_funct_2, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.77/0.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.77/0.98       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.77/0.98         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.77/0.98           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.77/0.98           ( m1_subset_1 @
% 0.77/0.98             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.77/0.98  thf('28', plain,
% 0.77/0.98      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.77/0.98         (~ (v2_funct_1 @ X37)
% 0.77/0.98          | ((k2_relset_1 @ X39 @ X38 @ X37) != (X38))
% 0.77/0.98          | (m1_subset_1 @ (k2_funct_1 @ X37) @ 
% 0.77/0.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.77/0.98          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 0.77/0.98          | ~ (v1_funct_2 @ X37 @ X39 @ X38)
% 0.77/0.98          | ~ (v1_funct_1 @ X37))),
% 0.77/0.98      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.77/0.98  thf('29', plain,
% 0.77/0.98      ((~ (v1_funct_1 @ sk_C)
% 0.77/0.98        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.77/0.98        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.77/0.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.77/0.98        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.77/0.98        | ~ (v2_funct_1 @ sk_C))),
% 0.77/0.98      inference('sup-', [status(thm)], ['27', '28'])).
% 0.77/0.98  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('32', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('33', plain, ((v2_funct_1 @ sk_C)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('34', plain,
% 0.77/0.98      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.77/0.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.77/0.98        | ((sk_B) != (sk_B)))),
% 0.77/0.98      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.77/0.98  thf('35', plain,
% 0.77/0.98      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.77/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.77/0.98      inference('simplify', [status(thm)], ['34'])).
% 0.77/0.98  thf('36', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.98         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.77/0.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.77/0.98          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.77/0.98          | ~ (v1_funct_1 @ X1))),
% 0.77/0.98      inference('demod', [status(thm)], ['14', '15'])).
% 0.77/0.98  thf('37', plain,
% 0.77/0.98      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.77/0.98        | (m1_subset_1 @ 
% 0.77/0.98           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 0.77/0.98            (k2_funct_1 @ sk_C)) @ 
% 0.77/0.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.77/0.98      inference('sup-', [status(thm)], ['35', '36'])).
% 0.77/0.98  thf('38', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('39', plain,
% 0.77/0.98      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.77/0.98         (~ (v2_funct_1 @ X37)
% 0.77/0.98          | ((k2_relset_1 @ X39 @ X38 @ X37) != (X38))
% 0.77/0.98          | (v1_funct_1 @ (k2_funct_1 @ X37))
% 0.77/0.98          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 0.77/0.98          | ~ (v1_funct_2 @ X37 @ X39 @ X38)
% 0.77/0.98          | ~ (v1_funct_1 @ X37))),
% 0.77/0.98      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.77/0.98  thf('40', plain,
% 0.77/0.98      ((~ (v1_funct_1 @ sk_C)
% 0.77/0.98        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.77/0.98        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.77/0.98        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.77/0.98        | ~ (v2_funct_1 @ sk_C))),
% 0.77/0.98      inference('sup-', [status(thm)], ['38', '39'])).
% 0.77/0.98  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('42', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('43', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('44', plain, ((v2_funct_1 @ sk_C)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('45', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)) | ((sk_B) != (sk_B)))),
% 0.77/0.98      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 0.77/0.98  thf('46', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.77/0.98      inference('simplify', [status(thm)], ['45'])).
% 0.77/0.98  thf('47', plain,
% 0.77/0.98      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.77/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.77/0.98      inference('simplify', [status(thm)], ['34'])).
% 0.77/0.98  thf('48', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.98         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.77/0.98            = (k5_relat_1 @ sk_C @ X0))
% 0.77/0.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.77/0.98          | ~ (v1_funct_1 @ X0))),
% 0.77/0.98      inference('demod', [status(thm)], ['4', '5'])).
% 0.77/0.98  thf('49', plain,
% 0.77/0.98      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.77/0.98        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 0.77/0.98            (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 0.77/0.98      inference('sup-', [status(thm)], ['47', '48'])).
% 0.77/0.98  thf('50', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.77/0.98      inference('simplify', [status(thm)], ['45'])).
% 0.77/0.98  thf('51', plain,
% 0.77/0.98      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C))
% 0.77/0.98         = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 0.77/0.98      inference('demod', [status(thm)], ['49', '50'])).
% 0.77/0.98  thf('52', plain,
% 0.77/0.98      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) @ 
% 0.77/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/0.98      inference('demod', [status(thm)], ['37', '46', '51'])).
% 0.77/0.98  thf('53', plain,
% 0.77/0.98      (((m1_subset_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 0.77/0.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.77/0.98        | ~ (v1_relat_1 @ sk_C)
% 0.77/0.98        | ~ (v1_funct_1 @ sk_C)
% 0.77/0.98        | ~ (v2_funct_1 @ sk_C))),
% 0.77/0.98      inference('sup+', [status(thm)], ['26', '52'])).
% 0.77/0.98  thf('54', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf(d1_funct_2, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.98       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.77/0.98           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.77/0.98             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.77/0.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.77/0.98           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.77/0.98             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.77/0.98  thf(zf_stmt_1, axiom,
% 0.77/0.98    (![C:$i,B:$i,A:$i]:
% 0.77/0.98     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.77/0.98       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.77/0.98  thf('55', plain,
% 0.77/0.98      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.77/0.98         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.77/0.98          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.77/0.98          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.77/0.98  thf('56', plain,
% 0.77/0.98      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.77/0.98        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.77/0.98      inference('sup-', [status(thm)], ['54', '55'])).
% 0.77/0.98  thf(zf_stmt_2, axiom,
% 0.77/0.98    (![B:$i,A:$i]:
% 0.77/0.98     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.77/0.98       ( zip_tseitin_0 @ B @ A ) ))).
% 0.77/0.98  thf('57', plain,
% 0.77/0.98      (![X16 : $i, X17 : $i]:
% 0.77/0.98         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.77/0.98  thf('58', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.77/0.98  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.77/0.98  thf(zf_stmt_5, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.98       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.77/0.98         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.77/0.98           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.77/0.98             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.77/0.98  thf('59', plain,
% 0.77/0.98      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.77/0.98         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.77/0.98          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.77/0.98          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.77/0.98  thf('60', plain,
% 0.77/0.98      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.77/0.98      inference('sup-', [status(thm)], ['58', '59'])).
% 0.77/0.98  thf('61', plain,
% 0.77/0.98      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.77/0.98      inference('sup-', [status(thm)], ['57', '60'])).
% 0.77/0.98  thf('62', plain, (((sk_B) != (k1_xboole_0))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('63', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.77/0.98      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.77/0.98  thf('64', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf(redefinition_k1_relset_1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.98       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.77/0.98  thf('65', plain,
% 0.77/0.98      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.77/0.98         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.77/0.98          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.77/0.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.77/0.98  thf('66', plain,
% 0.77/0.98      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.77/0.98      inference('sup-', [status(thm)], ['64', '65'])).
% 0.77/0.98  thf('67', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.77/0.98      inference('demod', [status(thm)], ['56', '63', '66'])).
% 0.77/0.98  thf('68', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf(cc1_relset_1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.98       ( v1_relat_1 @ C ) ))).
% 0.77/0.98  thf('69', plain,
% 0.77/0.98      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.77/0.98         ((v1_relat_1 @ X3)
% 0.77/0.98          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.77/0.98      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.77/0.98  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.77/0.98      inference('sup-', [status(thm)], ['68', '69'])).
% 0.77/0.98  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('72', plain, ((v2_funct_1 @ sk_C)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('73', plain,
% 0.77/0.98      ((m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.77/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/0.98      inference('demod', [status(thm)], ['53', '67', '70', '71', '72'])).
% 0.77/0.98  thf('74', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.77/0.98      inference('demod', [status(thm)], ['23', '73'])).
% 0.77/0.98  thf(t63_funct_1, axiom,
% 0.77/0.98    (![A:$i]:
% 0.77/0.98     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.98       ( ![B:$i]:
% 0.77/0.98         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.77/0.98           ( ( ( v2_funct_1 @ A ) & 
% 0.77/0.98               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.77/0.98               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.77/0.98             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.77/0.98  thf('75', plain,
% 0.77/0.98      (![X1 : $i, X2 : $i]:
% 0.77/0.98         (~ (v1_relat_1 @ X1)
% 0.77/0.98          | ~ (v1_funct_1 @ X1)
% 0.77/0.98          | ((X1) = (k2_funct_1 @ X2))
% 0.77/0.98          | ((k5_relat_1 @ X2 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X2)))
% 0.77/0.98          | ((k2_relat_1 @ X2) != (k1_relat_1 @ X1))
% 0.77/0.98          | ~ (v2_funct_1 @ X2)
% 0.77/0.98          | ~ (v1_funct_1 @ X2)
% 0.77/0.98          | ~ (v1_relat_1 @ X2))),
% 0.77/0.98      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.77/0.98  thf('76', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.77/0.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.77/0.98  thf('77', plain,
% 0.77/0.98      (![X1 : $i, X2 : $i]:
% 0.77/0.98         (~ (v1_relat_1 @ X1)
% 0.77/0.98          | ~ (v1_funct_1 @ X1)
% 0.77/0.98          | ((X1) = (k2_funct_1 @ X2))
% 0.77/0.98          | ((k5_relat_1 @ X2 @ X1) != (k6_partfun1 @ (k1_relat_1 @ X2)))
% 0.77/0.98          | ((k2_relat_1 @ X2) != (k1_relat_1 @ X1))
% 0.77/0.98          | ~ (v2_funct_1 @ X2)
% 0.77/0.98          | ~ (v1_funct_1 @ X2)
% 0.77/0.98          | ~ (v1_relat_1 @ X2))),
% 0.77/0.98      inference('demod', [status(thm)], ['75', '76'])).
% 0.77/0.98  thf('78', plain,
% 0.77/0.98      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.77/0.98        | ~ (v1_relat_1 @ sk_C)
% 0.77/0.98        | ~ (v1_funct_1 @ sk_C)
% 0.77/0.98        | ~ (v2_funct_1 @ sk_C)
% 0.77/0.98        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.77/0.98        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.77/0.98        | ~ (v1_funct_1 @ sk_D)
% 0.77/0.98        | ~ (v1_relat_1 @ sk_D))),
% 0.77/0.98      inference('sup-', [status(thm)], ['74', '77'])).
% 0.77/0.98  thf('79', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.77/0.98      inference('demod', [status(thm)], ['56', '63', '66'])).
% 0.77/0.98  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 0.77/0.98      inference('sup-', [status(thm)], ['68', '69'])).
% 0.77/0.98  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('82', plain, ((v2_funct_1 @ sk_C)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('83', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf(redefinition_k2_relset_1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.98       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.77/0.98  thf('84', plain,
% 0.77/0.98      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.77/0.98         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.77/0.98          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.77/0.98      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.77/0.98  thf('85', plain,
% 0.77/0.98      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.77/0.98      inference('sup-', [status(thm)], ['83', '84'])).
% 0.77/0.98  thf('86', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('87', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.77/0.98      inference('sup+', [status(thm)], ['85', '86'])).
% 0.77/0.98  thf('88', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('89', plain,
% 0.77/0.98      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.77/0.98         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.77/0.98          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.77/0.98          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.77/0.98  thf('90', plain,
% 0.77/0.98      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.77/0.98        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.77/0.98      inference('sup-', [status(thm)], ['88', '89'])).
% 0.77/0.98  thf('91', plain,
% 0.77/0.98      (![X16 : $i, X17 : $i]:
% 0.77/0.98         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.77/0.98  thf('92', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('93', plain,
% 0.77/0.98      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.77/0.98         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.77/0.98          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.77/0.98          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.77/0.98  thf('94', plain,
% 0.77/0.98      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.77/0.98      inference('sup-', [status(thm)], ['92', '93'])).
% 0.77/0.98  thf('95', plain,
% 0.77/0.98      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.77/0.98      inference('sup-', [status(thm)], ['91', '94'])).
% 0.77/0.98  thf('96', plain, (((sk_A) != (k1_xboole_0))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('97', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.77/0.98      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 0.77/0.98  thf('98', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('99', plain,
% 0.77/0.98      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.77/0.98         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.77/0.98          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.77/0.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.77/0.98  thf('100', plain,
% 0.77/0.98      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.77/0.98      inference('sup-', [status(thm)], ['98', '99'])).
% 0.77/0.98  thf('101', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.77/0.98      inference('demod', [status(thm)], ['90', '97', '100'])).
% 0.77/0.98  thf('102', plain, ((v1_funct_1 @ sk_D)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('103', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('104', plain,
% 0.77/0.98      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.77/0.98         ((v1_relat_1 @ X3)
% 0.77/0.98          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.77/0.98      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.77/0.98  thf('105', plain, ((v1_relat_1 @ sk_D)),
% 0.77/0.98      inference('sup-', [status(thm)], ['103', '104'])).
% 0.77/0.98  thf('106', plain,
% 0.77/0.98      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.77/0.98        | ((sk_B) != (sk_B))
% 0.77/0.98        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.77/0.98      inference('demod', [status(thm)],
% 0.77/0.98                ['78', '79', '80', '81', '82', '87', '101', '102', '105'])).
% 0.77/0.98  thf('107', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.77/0.98      inference('simplify', [status(thm)], ['106'])).
% 0.77/0.98  thf('108', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('109', plain, ($false),
% 0.77/0.98      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 0.77/0.98  
% 0.77/0.98  % SZS output end Refutation
% 0.77/0.98  
% 0.77/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
