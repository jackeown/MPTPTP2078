%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s3CoMd7RgS

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:11 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 782 expanded)
%              Number of leaves         :   43 ( 246 expanded)
%              Depth                    :   25
%              Number of atoms          : 1523 (16519 expanded)
%              Number of equality atoms :   61 ( 202 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('0',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('18',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('19',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('20',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('23',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X47 @ X45 @ X45 @ X46 @ X48 @ X44 ) )
      | ( v2_funct_1 @ X48 )
      | ( X46 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X45 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('29',plain,(
    ! [X9: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ k1_xboole_0 ) ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 )
        = ( k5_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ k1_xboole_0 @ sk_C @ sk_D )
        = ( k5_relat_1 @ sk_C @ sk_D ) ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('47',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('48',plain,
    ( ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ k1_xboole_0 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('51',plain,
    ( ( ( k1_partfun1 @ k1_xboole_0 @ sk_B @ sk_B @ k1_xboole_0 @ sk_C @ sk_D )
      = ( k6_relat_1 @ k1_xboole_0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = ( k5_relat_1 @ sk_C @ sk_D ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['43','44','45','51'])).

thf('53',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('55',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('56',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['54','55'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('57',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v4_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('60',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['58','61'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('63',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','64'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('66',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('68',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('69',plain,(
    ! [X6: $i] :
      ( ( ( k1_relat_1 @ X6 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X6 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('70',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ( ( k2_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['59','60'])).

thf('72',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['72'])).

thf(t47_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) )
           => ( v2_funct_1 @ B ) ) ) ) )).

thf('74',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X7 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
        | ( v2_funct_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['59','60'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
        | ( v2_funct_1 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,
    ( ( ~ ( v2_funct_1 @ ( k6_relat_1 @ k1_xboole_0 ) )
      | ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','79'])).

thf('81',plain,(
    ! [X9: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('82',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('85',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['80','81','82','85'])).

thf('87',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['2','86'])).

thf('88',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('89',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','89'])).

thf('91',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('92',plain,(
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

thf('93',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( r2_relset_1 @ X41 @ X41 @ ( k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43 ) @ ( k6_partfun1 @ X41 ) )
      | ( ( k2_relset_1 @ X42 @ X41 @ X43 )
        = X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('94',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( r2_relset_1 @ X41 @ X41 @ ( k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43 ) @ ( k6_relat_1 @ X41 ) )
      | ( ( k2_relset_1 @ X42 @ X41 @ X43 )
        = X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('102',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 )
      | ( X19 != X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('103',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('106',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('107',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['100','104','107','108','109','110'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('112',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ X24 )
       != X23 )
      | ( v2_funct_2 @ X24 @ X23 )
      | ~ ( v5_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('113',plain,(
    ! [X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v5_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
      | ( v2_funct_2 @ X24 @ ( k2_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['111','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('117',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['100','104','107','108','109','110'])).

thf('119',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['83','84'])).

thf('120',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['114','117','118','119'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['90','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s3CoMd7RgS
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 470 iterations in 0.219s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.68  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.46/0.68  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.68  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.46/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.68  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.68  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.68  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.68  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.46/0.68  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.68  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.68  thf(t29_funct_2, conjecture,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.68       ( ![D:$i]:
% 0.46/0.68         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.46/0.68             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.46/0.68           ( ( r2_relset_1 @
% 0.46/0.68               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.46/0.68               ( k6_partfun1 @ A ) ) =>
% 0.46/0.68             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.68        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.68            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.68          ( ![D:$i]:
% 0.46/0.68            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.46/0.68                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.46/0.68              ( ( r2_relset_1 @
% 0.46/0.68                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.46/0.68                  ( k6_partfun1 @ A ) ) =>
% 0.46/0.68                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.46/0.68  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('1', plain,
% 0.46/0.68      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.46/0.68      inference('split', [status(esa)], ['0'])).
% 0.46/0.68  thf('2', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('split', [status(esa)], ['0'])).
% 0.46/0.68  thf('3', plain,
% 0.46/0.68      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.46/0.68        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.46/0.68        (k6_partfun1 @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(redefinition_k6_partfun1, axiom,
% 0.46/0.68    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.46/0.68  thf('4', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.46/0.68      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.46/0.68        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.46/0.68        (k6_relat_1 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.68  thf('6', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('7', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(dt_k1_partfun1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.68     ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.68         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.68         ( v1_funct_1 @ F ) & 
% 0.46/0.68         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.46/0.68       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.46/0.68         ( m1_subset_1 @
% 0.46/0.68           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.46/0.68           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.46/0.68  thf('8', plain,
% 0.46/0.68      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.46/0.68          | ~ (v1_funct_1 @ X25)
% 0.46/0.68          | ~ (v1_funct_1 @ X28)
% 0.46/0.68          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.46/0.68          | (m1_subset_1 @ (k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28) @ 
% 0.46/0.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X30))))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.46/0.68  thf('9', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.46/0.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.68          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.46/0.68          | ~ (v1_funct_1 @ X1)
% 0.46/0.68          | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.68  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.46/0.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.68          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.46/0.68          | ~ (v1_funct_1 @ X1))),
% 0.46/0.68      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      ((~ (v1_funct_1 @ sk_D)
% 0.46/0.68        | (m1_subset_1 @ 
% 0.46/0.68           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.46/0.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['6', '11'])).
% 0.46/0.68  thf('13', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      ((m1_subset_1 @ 
% 0.46/0.68        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.46/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.68  thf(redefinition_r2_relset_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.68       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.46/0.68  thf('15', plain,
% 0.46/0.68      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.46/0.68          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.46/0.68          | ((X19) = (X22))
% 0.46/0.68          | ~ (r2_relset_1 @ X20 @ X21 @ X19 @ X22))),
% 0.46/0.68      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.46/0.68  thf('16', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.46/0.68             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.46/0.68          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.46/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.68  thf('17', plain,
% 0.46/0.68      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.46/0.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.46/0.68        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.46/0.68            = (k6_relat_1 @ sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['5', '16'])).
% 0.46/0.68  thf(dt_k6_partfun1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( m1_subset_1 @
% 0.46/0.68         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.46/0.68       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.46/0.68  thf('18', plain,
% 0.46/0.68      (![X32 : $i]:
% 0.46/0.68         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 0.46/0.68          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.46/0.68  thf('19', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.46/0.68      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.46/0.68  thf('20', plain,
% 0.46/0.68      (![X32 : $i]:
% 0.46/0.68         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 0.46/0.68          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.46/0.68      inference('demod', [status(thm)], ['18', '19'])).
% 0.46/0.68  thf('21', plain,
% 0.46/0.68      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.46/0.68         = (k6_relat_1 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['17', '20'])).
% 0.46/0.68  thf('22', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t26_funct_2, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.68       ( ![E:$i]:
% 0.46/0.68         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.46/0.68             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.46/0.68           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.46/0.68             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.46/0.68               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.46/0.68  thf('23', plain,
% 0.46/0.68      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.46/0.68         (~ (v1_funct_1 @ X44)
% 0.46/0.68          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 0.46/0.68          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.46/0.68          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X45 @ X45 @ X46 @ X48 @ X44))
% 0.46/0.68          | (v2_funct_1 @ X48)
% 0.46/0.68          | ((X46) = (k1_xboole_0))
% 0.46/0.68          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.46/0.68          | ~ (v1_funct_2 @ X48 @ X47 @ X45)
% 0.46/0.68          | ~ (v1_funct_1 @ X48))),
% 0.46/0.68      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.46/0.68  thf('24', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (v1_funct_1 @ X0)
% 0.46/0.68          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.46/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.46/0.68          | ((sk_A) = (k1_xboole_0))
% 0.46/0.68          | (v2_funct_1 @ X0)
% 0.46/0.68          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.46/0.68          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.46/0.68          | ~ (v1_funct_1 @ sk_D))),
% 0.46/0.68      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.68  thf('25', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('27', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (v1_funct_1 @ X0)
% 0.46/0.68          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.46/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.46/0.68          | ((sk_A) = (k1_xboole_0))
% 0.46/0.68          | (v2_funct_1 @ X0)
% 0.46/0.68          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.46/0.68      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.46/0.68  thf('28', plain,
% 0.46/0.68      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.46/0.68        | (v2_funct_1 @ sk_C)
% 0.46/0.68        | ((sk_A) = (k1_xboole_0))
% 0.46/0.68        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.46/0.68        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.46/0.68        | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.68      inference('sup-', [status(thm)], ['21', '27'])).
% 0.46/0.68  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.46/0.68  thf('29', plain, (![X9 : $i]: (v2_funct_1 @ (k6_relat_1 @ X9))),
% 0.46/0.68      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.46/0.68  thf('30', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('33', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.46/0.68  thf('34', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('split', [status(esa)], ['0'])).
% 0.46/0.68  thf('35', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.68  thf('36', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('37', plain,
% 0.46/0.68      (((m1_subset_1 @ sk_D @ 
% 0.46/0.68         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ k1_xboole_0))))
% 0.46/0.68         <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['35', '36'])).
% 0.46/0.68  thf('38', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(redefinition_k1_partfun1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.68     ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.68         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.68         ( v1_funct_1 @ F ) & 
% 0.46/0.68         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.46/0.68       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.46/0.68  thf('39', plain,
% 0.46/0.68      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.46/0.68          | ~ (v1_funct_1 @ X33)
% 0.46/0.68          | ~ (v1_funct_1 @ X36)
% 0.46/0.68          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.46/0.68          | ((k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36)
% 0.46/0.68              = (k5_relat_1 @ X33 @ X36)))),
% 0.46/0.68      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.46/0.68  thf('40', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.46/0.68            = (k5_relat_1 @ sk_C @ X0))
% 0.46/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.46/0.68          | ~ (v1_funct_1 @ X0)
% 0.46/0.68          | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.68      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.68  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('42', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.46/0.68            = (k5_relat_1 @ sk_C @ X0))
% 0.46/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.46/0.68          | ~ (v1_funct_1 @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.68  thf('43', plain,
% 0.46/0.68      (((~ (v1_funct_1 @ sk_D)
% 0.46/0.68         | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ k1_xboole_0 @ sk_C @ sk_D)
% 0.46/0.68             = (k5_relat_1 @ sk_C @ sk_D))))
% 0.46/0.68         <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['37', '42'])).
% 0.46/0.68  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('45', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.68  thf('46', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.68  thf('47', plain,
% 0.46/0.68      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.46/0.68         = (k6_relat_1 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['17', '20'])).
% 0.46/0.68  thf('48', plain,
% 0.46/0.68      ((((k1_partfun1 @ sk_A @ sk_B @ sk_B @ k1_xboole_0 @ sk_C @ sk_D)
% 0.46/0.68          = (k6_relat_1 @ sk_A)))
% 0.46/0.68         <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['46', '47'])).
% 0.46/0.68  thf('49', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.68  thf('50', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.68  thf('51', plain,
% 0.46/0.68      ((((k1_partfun1 @ k1_xboole_0 @ sk_B @ sk_B @ k1_xboole_0 @ sk_C @ sk_D)
% 0.46/0.68          = (k6_relat_1 @ k1_xboole_0)))
% 0.46/0.68         <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.46/0.68  thf('52', plain,
% 0.46/0.68      ((((k6_relat_1 @ k1_xboole_0) = (k5_relat_1 @ sk_C @ sk_D)))
% 0.46/0.68         <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('demod', [status(thm)], ['43', '44', '45', '51'])).
% 0.46/0.68  thf('53', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.68  thf('54', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(cc2_relset_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.68  thf('55', plain,
% 0.46/0.68      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.68         ((v4_relat_1 @ X13 @ X14)
% 0.46/0.68          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.46/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.68  thf('56', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.46/0.68      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.68  thf(d18_relat_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ B ) =>
% 0.46/0.68       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.68  thf('57', plain,
% 0.46/0.68      (![X4 : $i, X5 : $i]:
% 0.46/0.68         (~ (v4_relat_1 @ X4 @ X5)
% 0.46/0.68          | (r1_tarski @ (k1_relat_1 @ X4) @ X5)
% 0.46/0.68          | ~ (v1_relat_1 @ X4))),
% 0.46/0.68      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.46/0.68  thf('58', plain,
% 0.46/0.68      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['56', '57'])).
% 0.46/0.68  thf('59', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(cc1_relset_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.68       ( v1_relat_1 @ C ) ))).
% 0.46/0.68  thf('60', plain,
% 0.46/0.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.68         ((v1_relat_1 @ X10)
% 0.46/0.68          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.46/0.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.68  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.68      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.68  thf('62', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.46/0.68      inference('demod', [status(thm)], ['58', '61'])).
% 0.46/0.68  thf(d10_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.68  thf('63', plain,
% 0.46/0.68      (![X0 : $i, X2 : $i]:
% 0.46/0.68         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.68  thf('64', plain,
% 0.46/0.68      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))
% 0.46/0.68        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.68  thf('65', plain,
% 0.46/0.68      (((~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.46/0.68         | ((sk_A) = (k1_relat_1 @ sk_C)))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['53', '64'])).
% 0.46/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.68  thf('66', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.46/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.68  thf('67', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.68  thf('68', plain,
% 0.46/0.68      ((((k1_xboole_0) = (k1_relat_1 @ sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.46/0.68  thf(t65_relat_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ A ) =>
% 0.46/0.68       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.68         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.68  thf('69', plain,
% 0.46/0.68      (![X6 : $i]:
% 0.46/0.68         (((k1_relat_1 @ X6) != (k1_xboole_0))
% 0.46/0.68          | ((k2_relat_1 @ X6) = (k1_xboole_0))
% 0.46/0.68          | ~ (v1_relat_1 @ X6))),
% 0.46/0.68      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.46/0.68  thf('70', plain,
% 0.46/0.68      (((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.68         | ~ (v1_relat_1 @ sk_C)
% 0.46/0.68         | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.68  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.68      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.68  thf('72', plain,
% 0.46/0.68      (((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.68         | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('demod', [status(thm)], ['70', '71'])).
% 0.46/0.68  thf('73', plain,
% 0.46/0.68      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['72'])).
% 0.46/0.68  thf(t47_funct_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.68           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.46/0.68               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 0.46/0.68             ( v2_funct_1 @ B ) ) ) ) ))).
% 0.46/0.68  thf('74', plain,
% 0.46/0.68      (![X7 : $i, X8 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X7)
% 0.46/0.68          | ~ (v1_funct_1 @ X7)
% 0.46/0.68          | (v2_funct_1 @ X7)
% 0.46/0.68          | ~ (r1_tarski @ (k2_relat_1 @ X7) @ (k1_relat_1 @ X8))
% 0.46/0.68          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 0.46/0.68          | ~ (v1_funct_1 @ X8)
% 0.46/0.68          | ~ (v1_relat_1 @ X8))),
% 0.46/0.68      inference('cnf', [status(esa)], [t47_funct_1])).
% 0.46/0.68  thf('75', plain,
% 0.46/0.68      ((![X0 : $i]:
% 0.46/0.68          (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.46/0.68           | ~ (v1_relat_1 @ X0)
% 0.46/0.68           | ~ (v1_funct_1 @ X0)
% 0.46/0.68           | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ X0))
% 0.46/0.68           | (v2_funct_1 @ sk_C)
% 0.46/0.68           | ~ (v1_funct_1 @ sk_C)
% 0.46/0.68           | ~ (v1_relat_1 @ sk_C)))
% 0.46/0.68         <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['73', '74'])).
% 0.46/0.68  thf('76', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.46/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.68  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.68      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.68  thf('79', plain,
% 0.46/0.68      ((![X0 : $i]:
% 0.46/0.68          (~ (v1_relat_1 @ X0)
% 0.46/0.68           | ~ (v1_funct_1 @ X0)
% 0.46/0.68           | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ X0))
% 0.46/0.68           | (v2_funct_1 @ sk_C)))
% 0.46/0.68         <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.46/0.68  thf('80', plain,
% 0.46/0.68      (((~ (v2_funct_1 @ (k6_relat_1 @ k1_xboole_0))
% 0.46/0.68         | (v2_funct_1 @ sk_C)
% 0.46/0.68         | ~ (v1_funct_1 @ sk_D)
% 0.46/0.68         | ~ (v1_relat_1 @ sk_D))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['52', '79'])).
% 0.46/0.68  thf('81', plain, (![X9 : $i]: (v2_funct_1 @ (k6_relat_1 @ X9))),
% 0.46/0.68      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.46/0.68  thf('82', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('83', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('84', plain,
% 0.46/0.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.68         ((v1_relat_1 @ X10)
% 0.46/0.68          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.46/0.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.68  thf('85', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.68      inference('sup-', [status(thm)], ['83', '84'])).
% 0.46/0.68  thf('86', plain, (((v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.46/0.68      inference('demod', [status(thm)], ['80', '81', '82', '85'])).
% 0.46/0.68  thf('87', plain, (((v2_funct_1 @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['2', '86'])).
% 0.46/0.68  thf('88', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 0.46/0.68      inference('split', [status(esa)], ['0'])).
% 0.46/0.68  thf('89', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.46/0.68      inference('sat_resolution*', [status(thm)], ['87', '88'])).
% 0.46/0.68  thf('90', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 0.46/0.68      inference('simpl_trail', [status(thm)], ['1', '89'])).
% 0.46/0.68  thf('91', plain,
% 0.46/0.68      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.46/0.68         = (k6_relat_1 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['17', '20'])).
% 0.46/0.68  thf('92', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t24_funct_2, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.68       ( ![D:$i]:
% 0.46/0.68         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.46/0.68             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.46/0.68           ( ( r2_relset_1 @
% 0.46/0.68               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.46/0.68               ( k6_partfun1 @ B ) ) =>
% 0.46/0.68             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.46/0.68  thf('93', plain,
% 0.46/0.68      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.46/0.68         (~ (v1_funct_1 @ X40)
% 0.46/0.68          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 0.46/0.68          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.46/0.68          | ~ (r2_relset_1 @ X41 @ X41 @ 
% 0.46/0.68               (k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43) @ 
% 0.46/0.68               (k6_partfun1 @ X41))
% 0.46/0.68          | ((k2_relset_1 @ X42 @ X41 @ X43) = (X41))
% 0.46/0.68          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.46/0.68          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 0.46/0.68          | ~ (v1_funct_1 @ X43))),
% 0.46/0.68      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.46/0.68  thf('94', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.46/0.68      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.46/0.68  thf('95', plain,
% 0.46/0.68      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.46/0.68         (~ (v1_funct_1 @ X40)
% 0.46/0.68          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 0.46/0.68          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.46/0.68          | ~ (r2_relset_1 @ X41 @ X41 @ 
% 0.46/0.68               (k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43) @ 
% 0.46/0.68               (k6_relat_1 @ X41))
% 0.46/0.68          | ((k2_relset_1 @ X42 @ X41 @ X43) = (X41))
% 0.46/0.68          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.46/0.68          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 0.46/0.68          | ~ (v1_funct_1 @ X43))),
% 0.46/0.68      inference('demod', [status(thm)], ['93', '94'])).
% 0.46/0.68  thf('96', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (v1_funct_1 @ X0)
% 0.46/0.68          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.46/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.46/0.68          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.46/0.68          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.46/0.68               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.46/0.68               (k6_relat_1 @ sk_A))
% 0.46/0.68          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.46/0.68          | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.68      inference('sup-', [status(thm)], ['92', '95'])).
% 0.46/0.68  thf('97', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('99', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (v1_funct_1 @ X0)
% 0.46/0.68          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.46/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.46/0.68          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.46/0.68          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.46/0.68               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.46/0.68               (k6_relat_1 @ sk_A)))),
% 0.46/0.68      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.46/0.68  thf('100', plain,
% 0.46/0.68      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.46/0.68           (k6_relat_1 @ sk_A))
% 0.46/0.68        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.46/0.68        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.46/0.68        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.46/0.68        | ~ (v1_funct_1 @ sk_D))),
% 0.46/0.68      inference('sup-', [status(thm)], ['91', '99'])).
% 0.46/0.68  thf('101', plain,
% 0.46/0.68      (![X32 : $i]:
% 0.46/0.68         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 0.46/0.68          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.46/0.68      inference('demod', [status(thm)], ['18', '19'])).
% 0.46/0.68  thf('102', plain,
% 0.46/0.68      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.46/0.68          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.46/0.68          | (r2_relset_1 @ X20 @ X21 @ X19 @ X22)
% 0.46/0.68          | ((X19) != (X22)))),
% 0.46/0.68      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.46/0.68  thf('103', plain,
% 0.46/0.68      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.68         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 0.46/0.68          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.46/0.68      inference('simplify', [status(thm)], ['102'])).
% 0.46/0.68  thf('104', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['101', '103'])).
% 0.46/0.68  thf('105', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.68       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.68  thf('106', plain,
% 0.46/0.68      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.68         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.46/0.68          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.46/0.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.68  thf('107', plain,
% 0.46/0.68      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.46/0.68      inference('sup-', [status(thm)], ['105', '106'])).
% 0.46/0.68  thf('108', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('109', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('110', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('111', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.46/0.68      inference('demod', [status(thm)],
% 0.46/0.68                ['100', '104', '107', '108', '109', '110'])).
% 0.46/0.68  thf(d3_funct_2, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.46/0.68       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.68  thf('112', plain,
% 0.46/0.68      (![X23 : $i, X24 : $i]:
% 0.46/0.68         (((k2_relat_1 @ X24) != (X23))
% 0.46/0.68          | (v2_funct_2 @ X24 @ X23)
% 0.46/0.68          | ~ (v5_relat_1 @ X24 @ X23)
% 0.46/0.68          | ~ (v1_relat_1 @ X24))),
% 0.46/0.68      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.46/0.68  thf('113', plain,
% 0.46/0.68      (![X24 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X24)
% 0.46/0.68          | ~ (v5_relat_1 @ X24 @ (k2_relat_1 @ X24))
% 0.46/0.68          | (v2_funct_2 @ X24 @ (k2_relat_1 @ X24)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['112'])).
% 0.46/0.68  thf('114', plain,
% 0.46/0.68      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.46/0.68        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.46/0.68        | ~ (v1_relat_1 @ sk_D))),
% 0.46/0.68      inference('sup-', [status(thm)], ['111', '113'])).
% 0.46/0.68  thf('115', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('116', plain,
% 0.46/0.68      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.68         ((v5_relat_1 @ X13 @ X15)
% 0.46/0.68          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.46/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.68  thf('117', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.46/0.68      inference('sup-', [status(thm)], ['115', '116'])).
% 0.46/0.68  thf('118', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.46/0.68      inference('demod', [status(thm)],
% 0.46/0.68                ['100', '104', '107', '108', '109', '110'])).
% 0.46/0.68  thf('119', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.68      inference('sup-', [status(thm)], ['83', '84'])).
% 0.46/0.68  thf('120', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.46/0.68      inference('demod', [status(thm)], ['114', '117', '118', '119'])).
% 0.46/0.68  thf('121', plain, ($false), inference('demod', [status(thm)], ['90', '120'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.46/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
