%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LXroXNdb5R

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:54 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 437 expanded)
%              Number of leaves         :   45 ( 147 expanded)
%              Depth                    :   18
%              Number of atoms          : 1498 (10694 expanded)
%              Number of equality atoms :  111 ( 775 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['4','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('31',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('32',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( X25 = X28 )
      | ~ ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','33'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('35',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('36',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ ( k1_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('38',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('39',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('40',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('41',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('43',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ( ( k5_relat_1 @ X45 @ ( k2_funct_1 @ X45 ) )
        = ( k6_partfun1 @ X46 ) )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X46 @ X44 @ X45 )
       != X44 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('44',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45','46','47','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('53',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X16 @ ( k2_funct_1 @ X16 ) ) )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('54',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('56',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('57',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','57','60','61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('65',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X45 ) @ X45 )
        = ( k6_partfun1 @ X44 ) )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X46 @ X44 @ X45 )
       != X44 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('68',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf('74',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf(t59_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('77',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 ) )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('78',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('86',plain,
    ( ( sk_A != sk_A )
    | ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['38','41','63','64','65','83','84','85'])).

thf('87',plain,(
    r1_tarski @ sk_B @ ( k1_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['10','87'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('89',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('90',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('91',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X10 ) ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['88','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('94',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('96',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('97',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('98',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k5_relat_1 @ X6 @ ( k5_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['95','105'])).

thf('107',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','57','60','61','62'])).

thf('108',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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

thf('109',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('110',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ X11 @ ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('111',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('112',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ X11 @ ( k6_partfun1 @ ( k2_relat_1 @ X11 ) ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['108','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['107','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('118',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('122',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','120','121'])).

thf('123',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['94','122'])).

thf('124',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['123','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LXroXNdb5R
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:50:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.73  % Solved by: fo/fo7.sh
% 0.50/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.73  % done 439 iterations in 0.275s
% 0.50/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.73  % SZS output start Refutation
% 0.50/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.73  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.50/0.73  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.50/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.50/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.50/0.73  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.50/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.50/0.73  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.50/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.50/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.73  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.50/0.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.50/0.73  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.50/0.73  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.50/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.50/0.73  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.50/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.73  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.50/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.50/0.73  thf(t36_funct_2, conjecture,
% 0.50/0.73    (![A:$i,B:$i,C:$i]:
% 0.50/0.73     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.50/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.73       ( ![D:$i]:
% 0.50/0.73         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.50/0.73             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.50/0.73           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.50/0.73               ( r2_relset_1 @
% 0.50/0.73                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.50/0.73                 ( k6_partfun1 @ A ) ) & 
% 0.50/0.73               ( v2_funct_1 @ C ) ) =>
% 0.50/0.73             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.50/0.73               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.50/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.50/0.73        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.50/0.73            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.73          ( ![D:$i]:
% 0.50/0.73            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.50/0.73                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.50/0.73              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.50/0.73                  ( r2_relset_1 @
% 0.50/0.73                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.50/0.73                    ( k6_partfun1 @ A ) ) & 
% 0.50/0.73                  ( v2_funct_1 @ C ) ) =>
% 0.50/0.73                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.50/0.73                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.50/0.73    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.50/0.73  thf('0', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf(cc2_relset_1, axiom,
% 0.50/0.73    (![A:$i,B:$i,C:$i]:
% 0.50/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.73       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.50/0.73  thf('1', plain,
% 0.50/0.73      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.73         ((v4_relat_1 @ X22 @ X23)
% 0.50/0.73          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.50/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.50/0.73  thf('2', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.50/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.50/0.73  thf(d18_relat_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( v1_relat_1 @ B ) =>
% 0.50/0.73       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.50/0.73  thf('3', plain,
% 0.50/0.73      (![X3 : $i, X4 : $i]:
% 0.50/0.73         (~ (v4_relat_1 @ X3 @ X4)
% 0.50/0.73          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.50/0.73          | ~ (v1_relat_1 @ X3))),
% 0.50/0.73      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.50/0.73  thf('4', plain,
% 0.50/0.73      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.50/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.73  thf('5', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf(cc1_relset_1, axiom,
% 0.50/0.73    (![A:$i,B:$i,C:$i]:
% 0.50/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.73       ( v1_relat_1 @ C ) ))).
% 0.50/0.73  thf('6', plain,
% 0.50/0.73      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.50/0.73         ((v1_relat_1 @ X19)
% 0.50/0.73          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.50/0.73      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.50/0.73  thf('7', plain, ((v1_relat_1 @ sk_D)),
% 0.50/0.73      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.73  thf('8', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.50/0.73      inference('demod', [status(thm)], ['4', '7'])).
% 0.50/0.73  thf(d10_xboole_0, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.73  thf('9', plain,
% 0.50/0.73      (![X0 : $i, X2 : $i]:
% 0.50/0.73         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.50/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.74  thf('10', plain,
% 0.50/0.74      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ sk_D))
% 0.50/0.74        | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['8', '9'])).
% 0.50/0.74  thf('11', plain,
% 0.50/0.74      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.50/0.74        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.50/0.74        (k6_partfun1 @ sk_A))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('12', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('13', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(redefinition_k1_partfun1, axiom,
% 0.50/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.50/0.74     ( ( ( v1_funct_1 @ E ) & 
% 0.50/0.74         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.50/0.74         ( v1_funct_1 @ F ) & 
% 0.50/0.74         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.50/0.74       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.50/0.74  thf('14', plain,
% 0.50/0.74      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.50/0.74         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.50/0.74          | ~ (v1_funct_1 @ X37)
% 0.50/0.74          | ~ (v1_funct_1 @ X40)
% 0.50/0.74          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.50/0.74          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 0.50/0.74              = (k5_relat_1 @ X37 @ X40)))),
% 0.50/0.74      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.50/0.74  thf('15', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.74         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.50/0.74            = (k5_relat_1 @ sk_C @ X0))
% 0.50/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.50/0.74          | ~ (v1_funct_1 @ X0)
% 0.50/0.74          | ~ (v1_funct_1 @ sk_C))),
% 0.50/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.50/0.74  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('17', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.74         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.50/0.74            = (k5_relat_1 @ sk_C @ X0))
% 0.50/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.50/0.74          | ~ (v1_funct_1 @ X0))),
% 0.50/0.74      inference('demod', [status(thm)], ['15', '16'])).
% 0.50/0.74  thf('18', plain,
% 0.50/0.74      ((~ (v1_funct_1 @ sk_D)
% 0.50/0.74        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.50/0.74            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['12', '17'])).
% 0.50/0.74  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('20', plain,
% 0.50/0.74      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.50/0.74         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.50/0.74      inference('demod', [status(thm)], ['18', '19'])).
% 0.50/0.74  thf('21', plain,
% 0.50/0.74      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.50/0.74        (k6_partfun1 @ sk_A))),
% 0.50/0.74      inference('demod', [status(thm)], ['11', '20'])).
% 0.50/0.74  thf('22', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('23', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(dt_k1_partfun1, axiom,
% 0.50/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.50/0.74     ( ( ( v1_funct_1 @ E ) & 
% 0.50/0.74         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.50/0.74         ( v1_funct_1 @ F ) & 
% 0.50/0.74         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.50/0.74       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.50/0.74         ( m1_subset_1 @
% 0.50/0.74           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.50/0.74           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.50/0.74  thf('24', plain,
% 0.50/0.74      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.50/0.74         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.50/0.74          | ~ (v1_funct_1 @ X29)
% 0.50/0.74          | ~ (v1_funct_1 @ X32)
% 0.50/0.74          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.50/0.74          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 0.50/0.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 0.50/0.74      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.50/0.74  thf('25', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.74         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.50/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.50/0.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.50/0.74          | ~ (v1_funct_1 @ X1)
% 0.50/0.74          | ~ (v1_funct_1 @ sk_C))),
% 0.50/0.74      inference('sup-', [status(thm)], ['23', '24'])).
% 0.50/0.74  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('27', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.74         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.50/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.50/0.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.50/0.74          | ~ (v1_funct_1 @ X1))),
% 0.50/0.74      inference('demod', [status(thm)], ['25', '26'])).
% 0.50/0.74  thf('28', plain,
% 0.50/0.74      ((~ (v1_funct_1 @ sk_D)
% 0.50/0.74        | (m1_subset_1 @ 
% 0.50/0.74           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.50/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.50/0.74      inference('sup-', [status(thm)], ['22', '27'])).
% 0.50/0.74  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('30', plain,
% 0.50/0.74      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.50/0.74         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.50/0.74      inference('demod', [status(thm)], ['18', '19'])).
% 0.50/0.74  thf('31', plain,
% 0.50/0.74      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.50/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.74      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.50/0.74  thf(redefinition_r2_relset_1, axiom,
% 0.50/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.74     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.50/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.74       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.50/0.74  thf('32', plain,
% 0.50/0.74      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.50/0.74         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.50/0.74          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.50/0.74          | ((X25) = (X28))
% 0.50/0.74          | ~ (r2_relset_1 @ X26 @ X27 @ X25 @ X28))),
% 0.50/0.74      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.50/0.74  thf('33', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.50/0.74          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.50/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.50/0.74      inference('sup-', [status(thm)], ['31', '32'])).
% 0.50/0.74  thf('34', plain,
% 0.50/0.74      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.50/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.50/0.74        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['21', '33'])).
% 0.50/0.74  thf(dt_k6_partfun1, axiom,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( m1_subset_1 @
% 0.50/0.74         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.50/0.74       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.50/0.74  thf('35', plain,
% 0.50/0.74      (![X36 : $i]:
% 0.50/0.74         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 0.50/0.74          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 0.50/0.74      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.50/0.74  thf('36', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.50/0.74      inference('demod', [status(thm)], ['34', '35'])).
% 0.50/0.74  thf(t27_funct_1, axiom,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.74       ( ![B:$i]:
% 0.50/0.74         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.50/0.74           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.50/0.74             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.50/0.74  thf('37', plain,
% 0.50/0.74      (![X13 : $i, X14 : $i]:
% 0.50/0.74         (~ (v1_relat_1 @ X13)
% 0.50/0.74          | ~ (v1_funct_1 @ X13)
% 0.50/0.74          | (r1_tarski @ (k2_relat_1 @ X13) @ (k1_relat_1 @ X14))
% 0.50/0.74          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X14)) != (k1_relat_1 @ X13))
% 0.50/0.74          | ~ (v1_funct_1 @ X14)
% 0.50/0.74          | ~ (v1_relat_1 @ X14))),
% 0.50/0.74      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.50/0.74  thf('38', plain,
% 0.50/0.74      ((((k1_relat_1 @ (k6_partfun1 @ sk_A)) != (k1_relat_1 @ sk_C))
% 0.50/0.74        | ~ (v1_relat_1 @ sk_D)
% 0.50/0.74        | ~ (v1_funct_1 @ sk_D)
% 0.50/0.74        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D))
% 0.50/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.74        | ~ (v1_relat_1 @ sk_C))),
% 0.50/0.74      inference('sup-', [status(thm)], ['36', '37'])).
% 0.50/0.74  thf(t71_relat_1, axiom,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.50/0.74       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.50/0.74  thf('39', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.50/0.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.50/0.74  thf(redefinition_k6_partfun1, axiom,
% 0.50/0.74    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.50/0.74  thf('40', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.50/0.74      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.50/0.74  thf('41', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 0.50/0.74      inference('demod', [status(thm)], ['39', '40'])).
% 0.50/0.74  thf('42', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(t35_funct_2, axiom,
% 0.50/0.74    (![A:$i,B:$i,C:$i]:
% 0.50/0.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.50/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.74       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.50/0.74         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.50/0.74           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.50/0.74             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.50/0.74  thf('43', plain,
% 0.50/0.74      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.50/0.74         (((X44) = (k1_xboole_0))
% 0.50/0.74          | ~ (v1_funct_1 @ X45)
% 0.50/0.74          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 0.50/0.74          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 0.50/0.74          | ((k5_relat_1 @ X45 @ (k2_funct_1 @ X45)) = (k6_partfun1 @ X46))
% 0.50/0.74          | ~ (v2_funct_1 @ X45)
% 0.50/0.74          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 0.50/0.74      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.50/0.74  thf('44', plain,
% 0.50/0.74      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.50/0.74        | ~ (v2_funct_1 @ sk_C)
% 0.50/0.74        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.50/0.74        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.50/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.74        | ((sk_B) = (k1_xboole_0)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['42', '43'])).
% 0.50/0.74  thf('45', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('46', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('47', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('49', plain,
% 0.50/0.74      ((((sk_B) != (sk_B))
% 0.50/0.74        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.50/0.74        | ((sk_B) = (k1_xboole_0)))),
% 0.50/0.74      inference('demod', [status(thm)], ['44', '45', '46', '47', '48'])).
% 0.50/0.74  thf('50', plain,
% 0.50/0.74      ((((sk_B) = (k1_xboole_0))
% 0.50/0.74        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.50/0.74      inference('simplify', [status(thm)], ['49'])).
% 0.50/0.74  thf('51', plain, (((sk_B) != (k1_xboole_0))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('52', plain,
% 0.50/0.74      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.50/0.74      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.50/0.74  thf(t58_funct_1, axiom,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.74       ( ( v2_funct_1 @ A ) =>
% 0.50/0.74         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.50/0.74             ( k1_relat_1 @ A ) ) & 
% 0.50/0.74           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.50/0.74             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.50/0.74  thf('53', plain,
% 0.50/0.74      (![X16 : $i]:
% 0.50/0.74         (~ (v2_funct_1 @ X16)
% 0.50/0.74          | ((k2_relat_1 @ (k5_relat_1 @ X16 @ (k2_funct_1 @ X16)))
% 0.50/0.74              = (k1_relat_1 @ X16))
% 0.50/0.74          | ~ (v1_funct_1 @ X16)
% 0.50/0.74          | ~ (v1_relat_1 @ X16))),
% 0.50/0.74      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.50/0.74  thf('54', plain,
% 0.50/0.74      ((((k2_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))
% 0.50/0.74        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.74        | ~ (v2_funct_1 @ sk_C))),
% 0.50/0.74      inference('sup+', [status(thm)], ['52', '53'])).
% 0.50/0.74  thf('55', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.50/0.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.50/0.74  thf('56', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.50/0.74      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.50/0.74  thf('57', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X9)) = (X9))),
% 0.50/0.74      inference('demod', [status(thm)], ['55', '56'])).
% 0.50/0.74  thf('58', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('59', plain,
% 0.50/0.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.50/0.74         ((v1_relat_1 @ X19)
% 0.50/0.74          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.50/0.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.50/0.74  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.74      inference('sup-', [status(thm)], ['58', '59'])).
% 0.50/0.74  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('62', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('63', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.50/0.74      inference('demod', [status(thm)], ['54', '57', '60', '61', '62'])).
% 0.50/0.74  thf('64', plain, ((v1_relat_1 @ sk_D)),
% 0.50/0.74      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.74  thf('65', plain, ((v1_funct_1 @ sk_D)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('66', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('67', plain,
% 0.50/0.74      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.50/0.74         (((X44) = (k1_xboole_0))
% 0.50/0.74          | ~ (v1_funct_1 @ X45)
% 0.50/0.74          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 0.50/0.74          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 0.50/0.74          | ((k5_relat_1 @ (k2_funct_1 @ X45) @ X45) = (k6_partfun1 @ X44))
% 0.50/0.74          | ~ (v2_funct_1 @ X45)
% 0.50/0.74          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 0.50/0.74      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.50/0.74  thf('68', plain,
% 0.50/0.74      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.50/0.74        | ~ (v2_funct_1 @ sk_C)
% 0.50/0.74        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 0.50/0.74        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.50/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.74        | ((sk_B) = (k1_xboole_0)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['66', '67'])).
% 0.50/0.74  thf('69', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('70', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('71', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('73', plain,
% 0.50/0.74      ((((sk_B) != (sk_B))
% 0.50/0.74        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 0.50/0.74        | ((sk_B) = (k1_xboole_0)))),
% 0.50/0.74      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 0.50/0.74  thf('74', plain,
% 0.50/0.74      ((((sk_B) = (k1_xboole_0))
% 0.50/0.74        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 0.50/0.74      inference('simplify', [status(thm)], ['73'])).
% 0.50/0.74  thf('75', plain, (((sk_B) != (k1_xboole_0))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('76', plain,
% 0.50/0.74      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.50/0.74      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 0.50/0.74  thf(t59_funct_1, axiom,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.74       ( ( v2_funct_1 @ A ) =>
% 0.50/0.74         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.50/0.74             ( k2_relat_1 @ A ) ) & 
% 0.50/0.74           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.50/0.74             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.50/0.74  thf('77', plain,
% 0.50/0.74      (![X17 : $i]:
% 0.50/0.74         (~ (v2_funct_1 @ X17)
% 0.50/0.74          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X17) @ X17))
% 0.50/0.74              = (k2_relat_1 @ X17))
% 0.50/0.74          | ~ (v1_funct_1 @ X17)
% 0.50/0.74          | ~ (v1_relat_1 @ X17))),
% 0.50/0.74      inference('cnf', [status(esa)], [t59_funct_1])).
% 0.50/0.74  thf('78', plain,
% 0.50/0.74      ((((k2_relat_1 @ (k6_partfun1 @ sk_B)) = (k2_relat_1 @ sk_C))
% 0.50/0.74        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.74        | ~ (v2_funct_1 @ sk_C))),
% 0.50/0.74      inference('sup+', [status(thm)], ['76', '77'])).
% 0.50/0.74  thf('79', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X9)) = (X9))),
% 0.50/0.74      inference('demod', [status(thm)], ['55', '56'])).
% 0.50/0.74  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.74      inference('sup-', [status(thm)], ['58', '59'])).
% 0.50/0.74  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('82', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('83', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.50/0.74      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 0.50/0.74  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.74      inference('sup-', [status(thm)], ['58', '59'])).
% 0.50/0.74  thf('86', plain,
% 0.50/0.74      ((((sk_A) != (sk_A)) | (r1_tarski @ sk_B @ (k1_relat_1 @ sk_D)))),
% 0.50/0.74      inference('demod', [status(thm)],
% 0.50/0.74                ['38', '41', '63', '64', '65', '83', '84', '85'])).
% 0.50/0.74  thf('87', plain, ((r1_tarski @ sk_B @ (k1_relat_1 @ sk_D))),
% 0.50/0.74      inference('simplify', [status(thm)], ['86'])).
% 0.50/0.74  thf('88', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.50/0.74      inference('demod', [status(thm)], ['10', '87'])).
% 0.50/0.74  thf(t78_relat_1, axiom,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( v1_relat_1 @ A ) =>
% 0.50/0.74       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.50/0.74  thf('89', plain,
% 0.50/0.74      (![X10 : $i]:
% 0.50/0.74         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X10)) @ X10) = (X10))
% 0.50/0.74          | ~ (v1_relat_1 @ X10))),
% 0.50/0.74      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.50/0.74  thf('90', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.50/0.74      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.50/0.74  thf('91', plain,
% 0.50/0.74      (![X10 : $i]:
% 0.50/0.74         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X10)) @ X10) = (X10))
% 0.50/0.74          | ~ (v1_relat_1 @ X10))),
% 0.50/0.74      inference('demod', [status(thm)], ['89', '90'])).
% 0.50/0.74  thf('92', plain,
% 0.50/0.74      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))
% 0.50/0.74        | ~ (v1_relat_1 @ sk_D))),
% 0.50/0.74      inference('sup+', [status(thm)], ['88', '91'])).
% 0.50/0.74  thf('93', plain, ((v1_relat_1 @ sk_D)),
% 0.50/0.74      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.74  thf('94', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 0.50/0.74      inference('demod', [status(thm)], ['92', '93'])).
% 0.50/0.74  thf('95', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.50/0.74      inference('demod', [status(thm)], ['34', '35'])).
% 0.50/0.74  thf(dt_k2_funct_1, axiom,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.74       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.50/0.74         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.50/0.74  thf('96', plain,
% 0.50/0.74      (![X12 : $i]:
% 0.50/0.74         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 0.50/0.74          | ~ (v1_funct_1 @ X12)
% 0.50/0.74          | ~ (v1_relat_1 @ X12))),
% 0.50/0.74      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.50/0.74  thf('97', plain,
% 0.50/0.74      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.50/0.74      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 0.50/0.74  thf(t55_relat_1, axiom,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( v1_relat_1 @ A ) =>
% 0.50/0.74       ( ![B:$i]:
% 0.50/0.74         ( ( v1_relat_1 @ B ) =>
% 0.50/0.74           ( ![C:$i]:
% 0.50/0.74             ( ( v1_relat_1 @ C ) =>
% 0.50/0.74               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.50/0.74                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.50/0.74  thf('98', plain,
% 0.50/0.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.50/0.74         (~ (v1_relat_1 @ X5)
% 0.50/0.74          | ((k5_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 0.50/0.74              = (k5_relat_1 @ X6 @ (k5_relat_1 @ X5 @ X7)))
% 0.50/0.74          | ~ (v1_relat_1 @ X7)
% 0.50/0.74          | ~ (v1_relat_1 @ X6))),
% 0.50/0.74      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.50/0.74  thf('99', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.50/0.74            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 0.50/0.74          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.74          | ~ (v1_relat_1 @ X0)
% 0.50/0.74          | ~ (v1_relat_1 @ sk_C))),
% 0.50/0.74      inference('sup+', [status(thm)], ['97', '98'])).
% 0.50/0.74  thf('100', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.74      inference('sup-', [status(thm)], ['58', '59'])).
% 0.50/0.74  thf('101', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.50/0.74            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 0.50/0.74          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.74          | ~ (v1_relat_1 @ X0))),
% 0.50/0.74      inference('demod', [status(thm)], ['99', '100'])).
% 0.50/0.74  thf('102', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (~ (v1_relat_1 @ sk_C)
% 0.50/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.50/0.74          | ~ (v1_relat_1 @ X0)
% 0.50/0.74          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.50/0.74              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 0.50/0.74      inference('sup-', [status(thm)], ['96', '101'])).
% 0.50/0.74  thf('103', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.74      inference('sup-', [status(thm)], ['58', '59'])).
% 0.50/0.74  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('105', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (~ (v1_relat_1 @ X0)
% 0.50/0.74          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.50/0.74              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 0.50/0.74      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.50/0.74  thf('106', plain,
% 0.50/0.74      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 0.50/0.74          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 0.50/0.74        | ~ (v1_relat_1 @ sk_D))),
% 0.50/0.74      inference('sup+', [status(thm)], ['95', '105'])).
% 0.50/0.74  thf('107', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.50/0.74      inference('demod', [status(thm)], ['54', '57', '60', '61', '62'])).
% 0.50/0.74  thf('108', plain,
% 0.50/0.74      (![X12 : $i]:
% 0.50/0.74         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 0.50/0.74          | ~ (v1_funct_1 @ X12)
% 0.50/0.74          | ~ (v1_relat_1 @ X12))),
% 0.50/0.74      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.50/0.74  thf(t55_funct_1, axiom,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.74       ( ( v2_funct_1 @ A ) =>
% 0.50/0.74         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.50/0.74           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.50/0.74  thf('109', plain,
% 0.50/0.74      (![X15 : $i]:
% 0.50/0.74         (~ (v2_funct_1 @ X15)
% 0.50/0.74          | ((k1_relat_1 @ X15) = (k2_relat_1 @ (k2_funct_1 @ X15)))
% 0.50/0.74          | ~ (v1_funct_1 @ X15)
% 0.50/0.74          | ~ (v1_relat_1 @ X15))),
% 0.50/0.74      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.50/0.74  thf(t80_relat_1, axiom,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( v1_relat_1 @ A ) =>
% 0.50/0.74       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.50/0.74  thf('110', plain,
% 0.50/0.74      (![X11 : $i]:
% 0.50/0.74         (((k5_relat_1 @ X11 @ (k6_relat_1 @ (k2_relat_1 @ X11))) = (X11))
% 0.50/0.74          | ~ (v1_relat_1 @ X11))),
% 0.50/0.74      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.50/0.74  thf('111', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.50/0.74      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.50/0.74  thf('112', plain,
% 0.50/0.74      (![X11 : $i]:
% 0.50/0.74         (((k5_relat_1 @ X11 @ (k6_partfun1 @ (k2_relat_1 @ X11))) = (X11))
% 0.50/0.74          | ~ (v1_relat_1 @ X11))),
% 0.50/0.74      inference('demod', [status(thm)], ['110', '111'])).
% 0.50/0.74  thf('113', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.50/0.74            = (k2_funct_1 @ X0))
% 0.50/0.74          | ~ (v1_relat_1 @ X0)
% 0.50/0.74          | ~ (v1_funct_1 @ X0)
% 0.50/0.74          | ~ (v2_funct_1 @ X0)
% 0.50/0.74          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.50/0.74      inference('sup+', [status(thm)], ['109', '112'])).
% 0.50/0.74  thf('114', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (~ (v1_relat_1 @ X0)
% 0.50/0.74          | ~ (v1_funct_1 @ X0)
% 0.50/0.74          | ~ (v2_funct_1 @ X0)
% 0.50/0.74          | ~ (v1_funct_1 @ X0)
% 0.50/0.74          | ~ (v1_relat_1 @ X0)
% 0.50/0.74          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.50/0.74              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['108', '113'])).
% 0.50/0.74  thf('115', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.50/0.74            = (k2_funct_1 @ X0))
% 0.50/0.74          | ~ (v2_funct_1 @ X0)
% 0.50/0.74          | ~ (v1_funct_1 @ X0)
% 0.50/0.74          | ~ (v1_relat_1 @ X0))),
% 0.50/0.74      inference('simplify', [status(thm)], ['114'])).
% 0.50/0.74  thf('116', plain,
% 0.50/0.74      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.50/0.74          = (k2_funct_1 @ sk_C))
% 0.50/0.74        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.74        | ~ (v2_funct_1 @ sk_C))),
% 0.50/0.74      inference('sup+', [status(thm)], ['107', '115'])).
% 0.50/0.74  thf('117', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.74      inference('sup-', [status(thm)], ['58', '59'])).
% 0.50/0.74  thf('118', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('119', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('120', plain,
% 0.50/0.74      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.50/0.74         = (k2_funct_1 @ sk_C))),
% 0.50/0.74      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 0.50/0.74  thf('121', plain, ((v1_relat_1 @ sk_D)),
% 0.50/0.74      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.74  thf('122', plain,
% 0.50/0.74      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 0.50/0.74      inference('demod', [status(thm)], ['106', '120', '121'])).
% 0.50/0.74  thf('123', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.50/0.74      inference('sup+', [status(thm)], ['94', '122'])).
% 0.50/0.74  thf('124', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('125', plain, ($false),
% 0.50/0.74      inference('simplify_reflect-', [status(thm)], ['123', '124'])).
% 0.50/0.74  
% 0.50/0.74  % SZS output end Refutation
% 0.50/0.74  
% 0.50/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
