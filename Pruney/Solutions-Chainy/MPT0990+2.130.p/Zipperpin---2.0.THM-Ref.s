%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.smU27uQ4xU

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:17 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 847 expanded)
%              Number of leaves         :   42 ( 285 expanded)
%              Depth                    :   19
%              Number of atoms          : 1655 (12866 expanded)
%              Number of equality atoms :   89 ( 804 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 )
        = ( k5_relat_1 @ X33 @ X36 ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X32 ) ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
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

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('24',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v2_funct_1 @ X40 )
      | ( ( k2_relset_1 @ X42 @ X41 @ X40 )
       != X41 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['30','31','32','33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X15 ) @ X15 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('42',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('43',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X15 ) @ X15 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('49',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('50',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','52','57','58','59'])).

thf('61',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['27','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('63',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('64',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6
        = ( k7_relat_1 @ X6 @ X7 ) )
      | ~ ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('71',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['66','71'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('73',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('74',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('75',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('79',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['80','85'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('87',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ X11 @ ( k6_relat_1 @ X12 ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('88',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('89',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ X11 @ ( k6_partfun1 @ X12 ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('96',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['72','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['69','70'])).

thf('104',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['69','70'])).

thf('105',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['66','71'])).

thf('106',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['66','71'])).

thf('107',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) ),
    inference(demod,[status(thm)],['102','103','104','105','106'])).

thf('108',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('109',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) @ X0 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['107','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['69','70'])).

thf('118',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['69','70'])).

thf('119',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('120',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) ),
    inference(demod,[status(thm)],['102','103','104','105','106'])).

thf('121',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) ),
    inference(demod,[status(thm)],['102','103','104','105','106'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) @ sk_D )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('125',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['69','70'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) @ sk_D )
      = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_D @ X0 )
      = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120','126'])).

thf('128',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['66','71'])).

thf('129',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('130',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('131',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('133',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('135',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ X11 @ ( k6_partfun1 @ X12 ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('137',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('139',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['69','70'])).

thf('141',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','127','128','139','140'])).

thf('142',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['141','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.smU27uQ4xU
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.37/1.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.37/1.58  % Solved by: fo/fo7.sh
% 1.37/1.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.58  % done 1046 iterations in 1.113s
% 1.37/1.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.37/1.58  % SZS output start Refutation
% 1.37/1.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.37/1.58  thf(sk_C_type, type, sk_C: $i).
% 1.37/1.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.37/1.58  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.37/1.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.37/1.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.37/1.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.37/1.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.37/1.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.37/1.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.37/1.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.37/1.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.37/1.58  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.37/1.58  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.37/1.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.37/1.58  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.37/1.58  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.37/1.58  thf(sk_B_type, type, sk_B: $i).
% 1.37/1.58  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.37/1.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.37/1.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.37/1.58  thf(sk_D_type, type, sk_D: $i).
% 1.37/1.58  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.37/1.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.37/1.58  thf(t36_funct_2, conjecture,
% 1.37/1.58    (![A:$i,B:$i,C:$i]:
% 1.37/1.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.37/1.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.37/1.58       ( ![D:$i]:
% 1.37/1.58         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.37/1.58             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.37/1.58           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.37/1.58               ( r2_relset_1 @
% 1.37/1.58                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.37/1.58                 ( k6_partfun1 @ A ) ) & 
% 1.37/1.58               ( v2_funct_1 @ C ) ) =>
% 1.37/1.58             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.37/1.58               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.37/1.58  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.58    (~( ![A:$i,B:$i,C:$i]:
% 1.37/1.58        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.37/1.58            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.37/1.58          ( ![D:$i]:
% 1.37/1.58            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.37/1.58                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.37/1.58              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.37/1.58                  ( r2_relset_1 @
% 1.37/1.58                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.37/1.58                    ( k6_partfun1 @ A ) ) & 
% 1.37/1.58                  ( v2_funct_1 @ C ) ) =>
% 1.37/1.58                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.37/1.58                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.37/1.58    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.37/1.58  thf('0', plain,
% 1.37/1.58      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.37/1.58        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.37/1.58        (k6_partfun1 @ sk_A))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('1', plain,
% 1.37/1.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('2', plain,
% 1.37/1.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf(redefinition_k1_partfun1, axiom,
% 1.37/1.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.37/1.58     ( ( ( v1_funct_1 @ E ) & 
% 1.37/1.58         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.37/1.58         ( v1_funct_1 @ F ) & 
% 1.37/1.58         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.37/1.58       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.37/1.58  thf('3', plain,
% 1.37/1.58      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.37/1.58         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.37/1.58          | ~ (v1_funct_1 @ X33)
% 1.37/1.58          | ~ (v1_funct_1 @ X36)
% 1.37/1.58          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.37/1.58          | ((k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36)
% 1.37/1.58              = (k5_relat_1 @ X33 @ X36)))),
% 1.37/1.58      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.37/1.58  thf('4', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.58         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.37/1.58            = (k5_relat_1 @ sk_C @ X0))
% 1.37/1.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.37/1.58          | ~ (v1_funct_1 @ X0)
% 1.37/1.58          | ~ (v1_funct_1 @ sk_C))),
% 1.37/1.58      inference('sup-', [status(thm)], ['2', '3'])).
% 1.37/1.58  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('6', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.58         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.37/1.58            = (k5_relat_1 @ sk_C @ X0))
% 1.37/1.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.37/1.58          | ~ (v1_funct_1 @ X0))),
% 1.37/1.58      inference('demod', [status(thm)], ['4', '5'])).
% 1.37/1.58  thf('7', plain,
% 1.37/1.58      ((~ (v1_funct_1 @ sk_D)
% 1.37/1.58        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.37/1.58            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.37/1.58      inference('sup-', [status(thm)], ['1', '6'])).
% 1.37/1.58  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('9', plain,
% 1.37/1.58      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.37/1.58         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.37/1.58      inference('demod', [status(thm)], ['7', '8'])).
% 1.37/1.58  thf('10', plain,
% 1.37/1.58      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.37/1.58        (k6_partfun1 @ sk_A))),
% 1.37/1.58      inference('demod', [status(thm)], ['0', '9'])).
% 1.37/1.58  thf('11', plain,
% 1.37/1.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('12', plain,
% 1.37/1.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf(dt_k1_partfun1, axiom,
% 1.37/1.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.37/1.58     ( ( ( v1_funct_1 @ E ) & 
% 1.37/1.58         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.37/1.58         ( v1_funct_1 @ F ) & 
% 1.37/1.58         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.37/1.58       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.37/1.58         ( m1_subset_1 @
% 1.37/1.58           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.37/1.58           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.37/1.58  thf('13', plain,
% 1.37/1.58      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.37/1.58         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.37/1.58          | ~ (v1_funct_1 @ X27)
% 1.37/1.58          | ~ (v1_funct_1 @ X30)
% 1.37/1.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.37/1.58          | (m1_subset_1 @ (k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30) @ 
% 1.37/1.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X32))))),
% 1.37/1.58      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.37/1.58  thf('14', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.58         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.37/1.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.37/1.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.37/1.58          | ~ (v1_funct_1 @ X1)
% 1.37/1.58          | ~ (v1_funct_1 @ sk_C))),
% 1.37/1.58      inference('sup-', [status(thm)], ['12', '13'])).
% 1.37/1.58  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('16', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.58         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.37/1.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.37/1.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.37/1.58          | ~ (v1_funct_1 @ X1))),
% 1.37/1.58      inference('demod', [status(thm)], ['14', '15'])).
% 1.37/1.58  thf('17', plain,
% 1.37/1.58      ((~ (v1_funct_1 @ sk_D)
% 1.37/1.58        | (m1_subset_1 @ 
% 1.37/1.58           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.37/1.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.37/1.58      inference('sup-', [status(thm)], ['11', '16'])).
% 1.37/1.58  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('19', plain,
% 1.37/1.58      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.37/1.58         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.37/1.58      inference('demod', [status(thm)], ['7', '8'])).
% 1.37/1.58  thf('20', plain,
% 1.37/1.58      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.37/1.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.37/1.58      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.37/1.58  thf(redefinition_r2_relset_1, axiom,
% 1.37/1.58    (![A:$i,B:$i,C:$i,D:$i]:
% 1.37/1.58     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.37/1.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.37/1.58       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.37/1.58  thf('21', plain,
% 1.37/1.58      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.37/1.58         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.37/1.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.37/1.58          | ((X22) = (X25))
% 1.37/1.58          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 1.37/1.58      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.37/1.58  thf('22', plain,
% 1.37/1.58      (![X0 : $i]:
% 1.37/1.58         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.37/1.58          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.37/1.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.37/1.58      inference('sup-', [status(thm)], ['20', '21'])).
% 1.37/1.58  thf('23', plain,
% 1.37/1.58      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.37/1.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.37/1.58        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.37/1.58      inference('sup-', [status(thm)], ['10', '22'])).
% 1.37/1.58  thf(t29_relset_1, axiom,
% 1.37/1.58    (![A:$i]:
% 1.37/1.58     ( m1_subset_1 @
% 1.37/1.58       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.37/1.58  thf('24', plain,
% 1.37/1.58      (![X26 : $i]:
% 1.37/1.58         (m1_subset_1 @ (k6_relat_1 @ X26) @ 
% 1.37/1.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 1.37/1.58      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.37/1.58  thf(redefinition_k6_partfun1, axiom,
% 1.37/1.58    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.37/1.58  thf('25', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.37/1.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.37/1.58  thf('26', plain,
% 1.37/1.58      (![X26 : $i]:
% 1.37/1.58         (m1_subset_1 @ (k6_partfun1 @ X26) @ 
% 1.37/1.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 1.37/1.58      inference('demod', [status(thm)], ['24', '25'])).
% 1.37/1.58  thf('27', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.37/1.58      inference('demod', [status(thm)], ['23', '26'])).
% 1.37/1.58  thf('28', plain,
% 1.37/1.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf(t31_funct_2, axiom,
% 1.37/1.58    (![A:$i,B:$i,C:$i]:
% 1.37/1.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.37/1.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.37/1.58       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.37/1.58         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.37/1.58           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.37/1.58           ( m1_subset_1 @
% 1.37/1.58             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.37/1.58  thf('29', plain,
% 1.37/1.58      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.37/1.58         (~ (v2_funct_1 @ X40)
% 1.37/1.58          | ((k2_relset_1 @ X42 @ X41 @ X40) != (X41))
% 1.37/1.58          | (m1_subset_1 @ (k2_funct_1 @ X40) @ 
% 1.37/1.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.37/1.58          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 1.37/1.58          | ~ (v1_funct_2 @ X40 @ X42 @ X41)
% 1.37/1.58          | ~ (v1_funct_1 @ X40))),
% 1.37/1.58      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.37/1.58  thf('30', plain,
% 1.37/1.58      ((~ (v1_funct_1 @ sk_C)
% 1.37/1.58        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.37/1.58        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.37/1.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.37/1.58        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.37/1.58        | ~ (v2_funct_1 @ sk_C))),
% 1.37/1.58      inference('sup-', [status(thm)], ['28', '29'])).
% 1.37/1.58  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('32', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('33', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('34', plain, ((v2_funct_1 @ sk_C)),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('35', plain,
% 1.37/1.58      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.37/1.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.37/1.58        | ((sk_B) != (sk_B)))),
% 1.37/1.58      inference('demod', [status(thm)], ['30', '31', '32', '33', '34'])).
% 1.37/1.58  thf('36', plain,
% 1.37/1.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.37/1.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.37/1.58      inference('simplify', [status(thm)], ['35'])).
% 1.37/1.58  thf(cc2_relat_1, axiom,
% 1.37/1.58    (![A:$i]:
% 1.37/1.58     ( ( v1_relat_1 @ A ) =>
% 1.37/1.58       ( ![B:$i]:
% 1.37/1.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.37/1.58  thf('37', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.37/1.58          | (v1_relat_1 @ X0)
% 1.37/1.58          | ~ (v1_relat_1 @ X1))),
% 1.37/1.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.37/1.58  thf('38', plain,
% 1.37/1.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 1.37/1.58        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.37/1.58      inference('sup-', [status(thm)], ['36', '37'])).
% 1.37/1.58  thf(fc6_relat_1, axiom,
% 1.37/1.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.37/1.58  thf('39', plain,
% 1.37/1.58      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.37/1.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.37/1.58  thf('40', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.37/1.58      inference('demod', [status(thm)], ['38', '39'])).
% 1.37/1.58  thf(t61_funct_1, axiom,
% 1.37/1.58    (![A:$i]:
% 1.37/1.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.37/1.58       ( ( v2_funct_1 @ A ) =>
% 1.37/1.58         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.37/1.58             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.37/1.58           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.37/1.58             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.37/1.58  thf('41', plain,
% 1.37/1.58      (![X15 : $i]:
% 1.37/1.58         (~ (v2_funct_1 @ X15)
% 1.37/1.58          | ((k5_relat_1 @ (k2_funct_1 @ X15) @ X15)
% 1.37/1.58              = (k6_relat_1 @ (k2_relat_1 @ X15)))
% 1.37/1.58          | ~ (v1_funct_1 @ X15)
% 1.37/1.58          | ~ (v1_relat_1 @ X15))),
% 1.37/1.58      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.37/1.58  thf('42', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.37/1.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.37/1.58  thf('43', plain,
% 1.37/1.58      (![X15 : $i]:
% 1.37/1.58         (~ (v2_funct_1 @ X15)
% 1.37/1.58          | ((k5_relat_1 @ (k2_funct_1 @ X15) @ X15)
% 1.37/1.58              = (k6_partfun1 @ (k2_relat_1 @ X15)))
% 1.37/1.58          | ~ (v1_funct_1 @ X15)
% 1.37/1.58          | ~ (v1_relat_1 @ X15))),
% 1.37/1.58      inference('demod', [status(thm)], ['41', '42'])).
% 1.37/1.58  thf(t55_relat_1, axiom,
% 1.37/1.58    (![A:$i]:
% 1.37/1.58     ( ( v1_relat_1 @ A ) =>
% 1.37/1.58       ( ![B:$i]:
% 1.37/1.58         ( ( v1_relat_1 @ B ) =>
% 1.37/1.58           ( ![C:$i]:
% 1.37/1.58             ( ( v1_relat_1 @ C ) =>
% 1.37/1.58               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.37/1.58                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.37/1.58  thf('44', plain,
% 1.37/1.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.37/1.58         (~ (v1_relat_1 @ X8)
% 1.37/1.58          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 1.37/1.58              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 1.37/1.58          | ~ (v1_relat_1 @ X10)
% 1.37/1.58          | ~ (v1_relat_1 @ X9))),
% 1.37/1.58      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.37/1.58  thf('45', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 1.37/1.58            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 1.37/1.58          | ~ (v1_relat_1 @ X0)
% 1.37/1.58          | ~ (v1_funct_1 @ X0)
% 1.37/1.58          | ~ (v2_funct_1 @ X0)
% 1.37/1.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.37/1.58          | ~ (v1_relat_1 @ X1)
% 1.37/1.58          | ~ (v1_relat_1 @ X0))),
% 1.37/1.58      inference('sup+', [status(thm)], ['43', '44'])).
% 1.37/1.58  thf('46', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (~ (v1_relat_1 @ X1)
% 1.37/1.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.37/1.58          | ~ (v2_funct_1 @ X0)
% 1.37/1.58          | ~ (v1_funct_1 @ X0)
% 1.37/1.58          | ~ (v1_relat_1 @ X0)
% 1.37/1.58          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 1.37/1.58              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 1.37/1.58      inference('simplify', [status(thm)], ['45'])).
% 1.37/1.58  thf('47', plain,
% 1.37/1.58      (![X0 : $i]:
% 1.37/1.58         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ X0)
% 1.37/1.58            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.37/1.58          | ~ (v1_relat_1 @ sk_C)
% 1.37/1.58          | ~ (v1_funct_1 @ sk_C)
% 1.37/1.58          | ~ (v2_funct_1 @ sk_C)
% 1.37/1.58          | ~ (v1_relat_1 @ X0))),
% 1.37/1.58      inference('sup-', [status(thm)], ['40', '46'])).
% 1.37/1.58  thf('48', plain,
% 1.37/1.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf(redefinition_k2_relset_1, axiom,
% 1.37/1.58    (![A:$i,B:$i,C:$i]:
% 1.37/1.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.37/1.58  thf('49', plain,
% 1.37/1.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.37/1.58         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 1.37/1.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.37/1.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.37/1.58  thf('50', plain,
% 1.37/1.58      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.37/1.58      inference('sup-', [status(thm)], ['48', '49'])).
% 1.37/1.58  thf('51', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('52', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.37/1.58      inference('sup+', [status(thm)], ['50', '51'])).
% 1.37/1.58  thf('53', plain,
% 1.37/1.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('54', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.37/1.58          | (v1_relat_1 @ X0)
% 1.37/1.58          | ~ (v1_relat_1 @ X1))),
% 1.37/1.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.37/1.58  thf('55', plain,
% 1.37/1.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.37/1.58      inference('sup-', [status(thm)], ['53', '54'])).
% 1.37/1.58  thf('56', plain,
% 1.37/1.58      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.37/1.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.37/1.58  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 1.37/1.58      inference('demod', [status(thm)], ['55', '56'])).
% 1.37/1.58  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('59', plain, ((v2_funct_1 @ sk_C)),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('60', plain,
% 1.37/1.58      (![X0 : $i]:
% 1.37/1.58         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.37/1.58            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.37/1.58          | ~ (v1_relat_1 @ X0))),
% 1.37/1.58      inference('demod', [status(thm)], ['47', '52', '57', '58', '59'])).
% 1.37/1.58  thf('61', plain,
% 1.37/1.58      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.37/1.58          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.37/1.58        | ~ (v1_relat_1 @ sk_D))),
% 1.37/1.58      inference('sup+', [status(thm)], ['27', '60'])).
% 1.37/1.58  thf('62', plain,
% 1.37/1.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf(cc2_relset_1, axiom,
% 1.37/1.58    (![A:$i,B:$i,C:$i]:
% 1.37/1.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.37/1.58  thf('63', plain,
% 1.37/1.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.37/1.58         ((v4_relat_1 @ X16 @ X17)
% 1.37/1.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.37/1.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.37/1.58  thf('64', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.37/1.58      inference('sup-', [status(thm)], ['62', '63'])).
% 1.37/1.58  thf(t209_relat_1, axiom,
% 1.37/1.58    (![A:$i,B:$i]:
% 1.37/1.58     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.37/1.58       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.37/1.58  thf('65', plain,
% 1.37/1.58      (![X6 : $i, X7 : $i]:
% 1.37/1.58         (((X6) = (k7_relat_1 @ X6 @ X7))
% 1.37/1.58          | ~ (v4_relat_1 @ X6 @ X7)
% 1.37/1.58          | ~ (v1_relat_1 @ X6))),
% 1.37/1.58      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.37/1.58  thf('66', plain,
% 1.37/1.58      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_B)))),
% 1.37/1.58      inference('sup-', [status(thm)], ['64', '65'])).
% 1.37/1.58  thf('67', plain,
% 1.37/1.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('68', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.37/1.58          | (v1_relat_1 @ X0)
% 1.37/1.58          | ~ (v1_relat_1 @ X1))),
% 1.37/1.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.37/1.58  thf('69', plain,
% 1.37/1.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.37/1.58      inference('sup-', [status(thm)], ['67', '68'])).
% 1.37/1.58  thf('70', plain,
% 1.37/1.58      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.37/1.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.37/1.58  thf('71', plain, ((v1_relat_1 @ sk_D)),
% 1.37/1.58      inference('demod', [status(thm)], ['69', '70'])).
% 1.37/1.58  thf('72', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.37/1.58      inference('demod', [status(thm)], ['66', '71'])).
% 1.37/1.58  thf(t94_relat_1, axiom,
% 1.37/1.58    (![A:$i,B:$i]:
% 1.37/1.58     ( ( v1_relat_1 @ B ) =>
% 1.37/1.58       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.37/1.58  thf('73', plain,
% 1.37/1.58      (![X13 : $i, X14 : $i]:
% 1.37/1.58         (((k7_relat_1 @ X14 @ X13) = (k5_relat_1 @ (k6_relat_1 @ X13) @ X14))
% 1.37/1.58          | ~ (v1_relat_1 @ X14))),
% 1.37/1.58      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.37/1.58  thf('74', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.37/1.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.37/1.58  thf('75', plain,
% 1.37/1.58      (![X13 : $i, X14 : $i]:
% 1.37/1.58         (((k7_relat_1 @ X14 @ X13) = (k5_relat_1 @ (k6_partfun1 @ X13) @ X14))
% 1.37/1.58          | ~ (v1_relat_1 @ X14))),
% 1.37/1.58      inference('demod', [status(thm)], ['73', '74'])).
% 1.37/1.58  thf('76', plain,
% 1.37/1.58      (![X26 : $i]:
% 1.37/1.58         (m1_subset_1 @ (k6_partfun1 @ X26) @ 
% 1.37/1.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 1.37/1.58      inference('demod', [status(thm)], ['24', '25'])).
% 1.37/1.58  thf('77', plain,
% 1.37/1.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.37/1.58         ((v5_relat_1 @ X16 @ X18)
% 1.37/1.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.37/1.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.37/1.58  thf('78', plain, (![X0 : $i]: (v5_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 1.37/1.58      inference('sup-', [status(thm)], ['76', '77'])).
% 1.37/1.58  thf(d19_relat_1, axiom,
% 1.37/1.58    (![A:$i,B:$i]:
% 1.37/1.58     ( ( v1_relat_1 @ B ) =>
% 1.37/1.58       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.37/1.58  thf('79', plain,
% 1.37/1.58      (![X2 : $i, X3 : $i]:
% 1.37/1.58         (~ (v5_relat_1 @ X2 @ X3)
% 1.37/1.58          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 1.37/1.58          | ~ (v1_relat_1 @ X2))),
% 1.37/1.58      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.37/1.58  thf('80', plain,
% 1.37/1.58      (![X0 : $i]:
% 1.37/1.58         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.37/1.58          | (r1_tarski @ (k2_relat_1 @ (k6_partfun1 @ X0)) @ X0))),
% 1.37/1.58      inference('sup-', [status(thm)], ['78', '79'])).
% 1.37/1.58  thf('81', plain,
% 1.37/1.58      (![X26 : $i]:
% 1.37/1.58         (m1_subset_1 @ (k6_partfun1 @ X26) @ 
% 1.37/1.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 1.37/1.58      inference('demod', [status(thm)], ['24', '25'])).
% 1.37/1.58  thf('82', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.37/1.58          | (v1_relat_1 @ X0)
% 1.37/1.58          | ~ (v1_relat_1 @ X1))),
% 1.37/1.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.37/1.58  thf('83', plain,
% 1.37/1.58      (![X0 : $i]:
% 1.37/1.58         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 1.37/1.58          | (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.37/1.58      inference('sup-', [status(thm)], ['81', '82'])).
% 1.37/1.58  thf('84', plain,
% 1.37/1.58      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.37/1.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.37/1.58  thf('85', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.37/1.58      inference('demod', [status(thm)], ['83', '84'])).
% 1.37/1.58  thf('86', plain,
% 1.37/1.58      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k6_partfun1 @ X0)) @ X0)),
% 1.37/1.58      inference('demod', [status(thm)], ['80', '85'])).
% 1.37/1.58  thf(t79_relat_1, axiom,
% 1.37/1.58    (![A:$i,B:$i]:
% 1.37/1.58     ( ( v1_relat_1 @ B ) =>
% 1.37/1.58       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.37/1.58         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 1.37/1.58  thf('87', plain,
% 1.37/1.58      (![X11 : $i, X12 : $i]:
% 1.37/1.58         (~ (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 1.37/1.58          | ((k5_relat_1 @ X11 @ (k6_relat_1 @ X12)) = (X11))
% 1.37/1.58          | ~ (v1_relat_1 @ X11))),
% 1.37/1.58      inference('cnf', [status(esa)], [t79_relat_1])).
% 1.37/1.58  thf('88', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.37/1.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.37/1.58  thf('89', plain,
% 1.37/1.58      (![X11 : $i, X12 : $i]:
% 1.37/1.58         (~ (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 1.37/1.58          | ((k5_relat_1 @ X11 @ (k6_partfun1 @ X12)) = (X11))
% 1.37/1.58          | ~ (v1_relat_1 @ X11))),
% 1.37/1.58      inference('demod', [status(thm)], ['87', '88'])).
% 1.37/1.58  thf('90', plain,
% 1.37/1.58      (![X0 : $i]:
% 1.37/1.58         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.37/1.58          | ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.37/1.58              = (k6_partfun1 @ X0)))),
% 1.37/1.58      inference('sup-', [status(thm)], ['86', '89'])).
% 1.37/1.58  thf('91', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.37/1.58      inference('demod', [status(thm)], ['83', '84'])).
% 1.37/1.58  thf('92', plain,
% 1.37/1.58      (![X0 : $i]:
% 1.37/1.58         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.37/1.58           = (k6_partfun1 @ X0))),
% 1.37/1.58      inference('demod', [status(thm)], ['90', '91'])).
% 1.37/1.58  thf('93', plain,
% 1.37/1.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.37/1.58         (~ (v1_relat_1 @ X8)
% 1.37/1.58          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 1.37/1.58              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 1.37/1.58          | ~ (v1_relat_1 @ X10)
% 1.37/1.58          | ~ (v1_relat_1 @ X9))),
% 1.37/1.58      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.37/1.58  thf('94', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((k5_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 1.37/1.58            = (k5_relat_1 @ (k6_partfun1 @ X0) @ 
% 1.37/1.58               (k5_relat_1 @ (k6_partfun1 @ X0) @ X1)))
% 1.37/1.58          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.37/1.58          | ~ (v1_relat_1 @ X1)
% 1.37/1.58          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.37/1.58      inference('sup+', [status(thm)], ['92', '93'])).
% 1.37/1.58  thf('95', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.37/1.58      inference('demod', [status(thm)], ['83', '84'])).
% 1.37/1.58  thf('96', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.37/1.58      inference('demod', [status(thm)], ['83', '84'])).
% 1.37/1.58  thf('97', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((k5_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 1.37/1.58            = (k5_relat_1 @ (k6_partfun1 @ X0) @ 
% 1.37/1.58               (k5_relat_1 @ (k6_partfun1 @ X0) @ X1)))
% 1.37/1.58          | ~ (v1_relat_1 @ X1))),
% 1.37/1.58      inference('demod', [status(thm)], ['94', '95', '96'])).
% 1.37/1.58  thf('98', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((k5_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 1.37/1.58            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k7_relat_1 @ X1 @ X0)))
% 1.37/1.58          | ~ (v1_relat_1 @ X1)
% 1.37/1.58          | ~ (v1_relat_1 @ X1))),
% 1.37/1.58      inference('sup+', [status(thm)], ['75', '97'])).
% 1.37/1.58  thf('99', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (~ (v1_relat_1 @ X1)
% 1.37/1.58          | ((k5_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 1.37/1.58              = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k7_relat_1 @ X1 @ X0))))),
% 1.37/1.58      inference('simplify', [status(thm)], ['98'])).
% 1.37/1.58  thf('100', plain,
% 1.37/1.58      (![X13 : $i, X14 : $i]:
% 1.37/1.58         (((k7_relat_1 @ X14 @ X13) = (k5_relat_1 @ (k6_partfun1 @ X13) @ X14))
% 1.37/1.58          | ~ (v1_relat_1 @ X14))),
% 1.37/1.58      inference('demod', [status(thm)], ['73', '74'])).
% 1.37/1.58  thf('101', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X1)
% 1.37/1.58            = (k5_relat_1 @ (k6_partfun1 @ X1) @ X0))
% 1.37/1.58          | ~ (v1_relat_1 @ X0)
% 1.37/1.58          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 1.37/1.58      inference('sup+', [status(thm)], ['99', '100'])).
% 1.37/1.58  thf('102', plain,
% 1.37/1.58      ((~ (v1_relat_1 @ sk_D)
% 1.37/1.58        | ~ (v1_relat_1 @ sk_D)
% 1.37/1.58        | ((k7_relat_1 @ (k7_relat_1 @ sk_D @ sk_B) @ sk_B)
% 1.37/1.58            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)))),
% 1.37/1.58      inference('sup-', [status(thm)], ['72', '101'])).
% 1.37/1.58  thf('103', plain, ((v1_relat_1 @ sk_D)),
% 1.37/1.58      inference('demod', [status(thm)], ['69', '70'])).
% 1.37/1.58  thf('104', plain, ((v1_relat_1 @ sk_D)),
% 1.37/1.58      inference('demod', [status(thm)], ['69', '70'])).
% 1.37/1.58  thf('105', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.37/1.58      inference('demod', [status(thm)], ['66', '71'])).
% 1.37/1.58  thf('106', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.37/1.58      inference('demod', [status(thm)], ['66', '71'])).
% 1.37/1.58  thf('107', plain, (((sk_D) = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D))),
% 1.37/1.58      inference('demod', [status(thm)], ['102', '103', '104', '105', '106'])).
% 1.37/1.58  thf('108', plain,
% 1.37/1.58      (![X13 : $i, X14 : $i]:
% 1.37/1.58         (((k7_relat_1 @ X14 @ X13) = (k5_relat_1 @ (k6_partfun1 @ X13) @ X14))
% 1.37/1.58          | ~ (v1_relat_1 @ X14))),
% 1.37/1.58      inference('demod', [status(thm)], ['73', '74'])).
% 1.37/1.58  thf('109', plain,
% 1.37/1.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.37/1.58         (~ (v1_relat_1 @ X8)
% 1.37/1.58          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 1.37/1.58              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 1.37/1.58          | ~ (v1_relat_1 @ X10)
% 1.37/1.58          | ~ (v1_relat_1 @ X9))),
% 1.37/1.58      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.37/1.58  thf('110', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.58         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.37/1.58            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 1.37/1.58          | ~ (v1_relat_1 @ X1)
% 1.37/1.58          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.37/1.58          | ~ (v1_relat_1 @ X2)
% 1.37/1.58          | ~ (v1_relat_1 @ X1))),
% 1.37/1.58      inference('sup+', [status(thm)], ['108', '109'])).
% 1.37/1.58  thf('111', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.37/1.58      inference('demod', [status(thm)], ['83', '84'])).
% 1.37/1.58  thf('112', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.58         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.37/1.58            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 1.37/1.58          | ~ (v1_relat_1 @ X1)
% 1.37/1.58          | ~ (v1_relat_1 @ X2)
% 1.37/1.58          | ~ (v1_relat_1 @ X1))),
% 1.37/1.58      inference('demod', [status(thm)], ['110', '111'])).
% 1.37/1.58  thf('113', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.58         (~ (v1_relat_1 @ X2)
% 1.37/1.58          | ~ (v1_relat_1 @ X1)
% 1.37/1.58          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.37/1.58              = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 1.37/1.58      inference('simplify', [status(thm)], ['112'])).
% 1.37/1.58  thf('114', plain,
% 1.37/1.58      (![X13 : $i, X14 : $i]:
% 1.37/1.58         (((k7_relat_1 @ X14 @ X13) = (k5_relat_1 @ (k6_partfun1 @ X13) @ X14))
% 1.37/1.58          | ~ (v1_relat_1 @ X14))),
% 1.37/1.58      inference('demod', [status(thm)], ['73', '74'])).
% 1.37/1.58  thf('115', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.58         (((k7_relat_1 @ (k5_relat_1 @ X2 @ X0) @ X1)
% 1.37/1.58            = (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 1.37/1.58          | ~ (v1_relat_1 @ X2)
% 1.37/1.58          | ~ (v1_relat_1 @ X0)
% 1.37/1.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 1.37/1.58      inference('sup+', [status(thm)], ['113', '114'])).
% 1.37/1.58  thf('116', plain,
% 1.37/1.58      (![X0 : $i]:
% 1.37/1.58         (~ (v1_relat_1 @ sk_D)
% 1.37/1.58          | ~ (v1_relat_1 @ sk_D)
% 1.37/1.58          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 1.37/1.58          | ((k7_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) @ X0)
% 1.37/1.58              = (k5_relat_1 @ (k7_relat_1 @ (k6_partfun1 @ sk_B) @ X0) @ sk_D)))),
% 1.37/1.58      inference('sup-', [status(thm)], ['107', '115'])).
% 1.37/1.58  thf('117', plain, ((v1_relat_1 @ sk_D)),
% 1.37/1.58      inference('demod', [status(thm)], ['69', '70'])).
% 1.37/1.58  thf('118', plain, ((v1_relat_1 @ sk_D)),
% 1.37/1.58      inference('demod', [status(thm)], ['69', '70'])).
% 1.37/1.58  thf('119', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.37/1.58      inference('demod', [status(thm)], ['83', '84'])).
% 1.37/1.58  thf('120', plain, (((sk_D) = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D))),
% 1.37/1.58      inference('demod', [status(thm)], ['102', '103', '104', '105', '106'])).
% 1.37/1.58  thf('121', plain, (((sk_D) = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D))),
% 1.37/1.58      inference('demod', [status(thm)], ['102', '103', '104', '105', '106'])).
% 1.37/1.58  thf('122', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.58         (~ (v1_relat_1 @ X2)
% 1.37/1.58          | ~ (v1_relat_1 @ X1)
% 1.37/1.58          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.37/1.58              = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 1.37/1.58      inference('simplify', [status(thm)], ['112'])).
% 1.37/1.58  thf('123', plain,
% 1.37/1.58      (![X0 : $i]:
% 1.37/1.58         (((k5_relat_1 @ (k7_relat_1 @ (k6_partfun1 @ sk_B) @ X0) @ sk_D)
% 1.37/1.58            = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))
% 1.37/1.58          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 1.37/1.58          | ~ (v1_relat_1 @ sk_D))),
% 1.37/1.58      inference('sup+', [status(thm)], ['121', '122'])).
% 1.37/1.58  thf('124', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.37/1.58      inference('demod', [status(thm)], ['83', '84'])).
% 1.37/1.58  thf('125', plain, ((v1_relat_1 @ sk_D)),
% 1.37/1.58      inference('demod', [status(thm)], ['69', '70'])).
% 1.37/1.58  thf('126', plain,
% 1.37/1.58      (![X0 : $i]:
% 1.37/1.58         ((k5_relat_1 @ (k7_relat_1 @ (k6_partfun1 @ sk_B) @ X0) @ sk_D)
% 1.37/1.58           = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))),
% 1.37/1.58      inference('demod', [status(thm)], ['123', '124', '125'])).
% 1.37/1.58  thf('127', plain,
% 1.37/1.58      (![X0 : $i]:
% 1.37/1.58         ((k7_relat_1 @ sk_D @ X0) = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))),
% 1.37/1.58      inference('demod', [status(thm)],
% 1.37/1.58                ['116', '117', '118', '119', '120', '126'])).
% 1.37/1.58  thf('128', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.37/1.58      inference('demod', [status(thm)], ['66', '71'])).
% 1.37/1.58  thf('129', plain,
% 1.37/1.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.37/1.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.37/1.58      inference('simplify', [status(thm)], ['35'])).
% 1.37/1.58  thf('130', plain,
% 1.37/1.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.37/1.58         ((v5_relat_1 @ X16 @ X18)
% 1.37/1.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.37/1.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.37/1.58  thf('131', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 1.37/1.58      inference('sup-', [status(thm)], ['129', '130'])).
% 1.37/1.58  thf('132', plain,
% 1.37/1.58      (![X2 : $i, X3 : $i]:
% 1.37/1.58         (~ (v5_relat_1 @ X2 @ X3)
% 1.37/1.58          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 1.37/1.58          | ~ (v1_relat_1 @ X2))),
% 1.37/1.58      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.37/1.58  thf('133', plain,
% 1.37/1.58      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.37/1.58        | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 1.37/1.58      inference('sup-', [status(thm)], ['131', '132'])).
% 1.37/1.58  thf('134', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.37/1.58      inference('demod', [status(thm)], ['38', '39'])).
% 1.37/1.58  thf('135', plain, ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 1.37/1.58      inference('demod', [status(thm)], ['133', '134'])).
% 1.37/1.58  thf('136', plain,
% 1.37/1.58      (![X11 : $i, X12 : $i]:
% 1.37/1.58         (~ (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 1.37/1.58          | ((k5_relat_1 @ X11 @ (k6_partfun1 @ X12)) = (X11))
% 1.37/1.58          | ~ (v1_relat_1 @ X11))),
% 1.37/1.58      inference('demod', [status(thm)], ['87', '88'])).
% 1.37/1.58  thf('137', plain,
% 1.37/1.58      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.37/1.58        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.37/1.58            = (k2_funct_1 @ sk_C)))),
% 1.37/1.58      inference('sup-', [status(thm)], ['135', '136'])).
% 1.37/1.58  thf('138', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.37/1.58      inference('demod', [status(thm)], ['38', '39'])).
% 1.37/1.58  thf('139', plain,
% 1.37/1.58      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.37/1.58         = (k2_funct_1 @ sk_C))),
% 1.37/1.58      inference('demod', [status(thm)], ['137', '138'])).
% 1.37/1.58  thf('140', plain, ((v1_relat_1 @ sk_D)),
% 1.37/1.58      inference('demod', [status(thm)], ['69', '70'])).
% 1.37/1.58  thf('141', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.37/1.58      inference('demod', [status(thm)], ['61', '127', '128', '139', '140'])).
% 1.37/1.58  thf('142', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('143', plain, ($false),
% 1.37/1.58      inference('simplify_reflect-', [status(thm)], ['141', '142'])).
% 1.37/1.58  
% 1.37/1.58  % SZS output end Refutation
% 1.37/1.58  
% 1.37/1.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
