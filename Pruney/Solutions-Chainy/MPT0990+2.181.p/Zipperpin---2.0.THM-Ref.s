%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2VyiCdwSm2

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:26 EST 2020

% Result     : Theorem 3.28s
% Output     : Refutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  218 (1312 expanded)
%              Number of leaves         :   47 ( 397 expanded)
%              Depth                    :   26
%              Number of atoms          : 2030 (35394 expanded)
%              Number of equality atoms :  150 (2363 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('4',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X4 ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('6',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('27',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('28',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X32 = X35 )
      | ~ ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('31',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('32',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('33',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','33'])).

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

thf('35',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( X24
        = ( k2_funct_1 @ X25 ) )
      | ( ( k5_relat_1 @ X24 @ X25 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X25 ) ) )
      | ( ( k2_relat_1 @ X24 )
       != ( k1_relat_1 @ X25 ) )
      | ~ ( v2_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('36',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('37',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( X24
        = ( k2_funct_1 @ X25 ) )
      | ( ( k5_relat_1 @ X24 @ X25 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X25 ) ) )
      | ( ( k2_relat_1 @ X24 )
       != ( k1_relat_1 @ X25 ) )
      | ~ ( v2_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
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

thf('41',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( r2_relset_1 @ X51 @ X51 @ ( k1_partfun1 @ X51 @ X52 @ X52 @ X51 @ X50 @ X53 ) @ ( k6_partfun1 @ X51 ) )
      | ( ( k2_relset_1 @ X52 @ X51 @ X53 )
        = X51 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('48',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('49',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['46','49','50','51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('55',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('58',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['38','53','54','55','60','61','66'])).

thf('68',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('70',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('71',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
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

thf('73',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_funct_2 @ X58 @ X59 @ X60 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) )
      | ( zip_tseitin_0 @ X58 @ X61 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X62 @ X59 @ X59 @ X60 @ X61 @ X58 ) )
      | ( zip_tseitin_1 @ X60 @ X59 )
      | ( ( k2_relset_1 @ X62 @ X59 @ X61 )
       != X59 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X59 ) ) )
      | ~ ( v1_funct_2 @ X61 @ X62 @ X59 )
      | ~ ( v1_funct_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('74',plain,(
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
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['71','77'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('79',plain,(
    ! [X17: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('80',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('81',plain,(
    ! [X17: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['78','81','82','83','84','85'])).

thf('87',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X56: $i,X57: $i] :
      ( ( X56 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('89',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X54: $i,X55: $i] :
      ( ( v2_funct_1 @ X55 )
      | ~ ( zip_tseitin_0 @ X55 @ X54 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('93',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['68','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('96',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('97',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('99',plain,
    ( ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['91','92'])).

thf('101',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_C
      = ( k4_relat_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['94','101'])).

thf('103',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['46','49','50','51','52'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('104',plain,(
    ! [X69: $i] :
      ( ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X69 ) @ ( k2_relat_1 @ X69 ) ) ) )
      | ~ ( v1_funct_1 @ X69 )
      | ~ ( v1_relat_1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('105',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('107',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

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

thf('109',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( X66 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X67 )
      | ~ ( v1_funct_2 @ X67 @ X68 @ X66 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X66 ) ) )
      | ( ( k5_relat_1 @ X67 @ ( k2_funct_1 @ X67 ) )
        = ( k6_partfun1 @ X68 ) )
      | ~ ( v2_funct_1 @ X67 )
      | ( ( k2_relset_1 @ X68 @ X66 @ X67 )
       != X66 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('110',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['46','49','50','51','52'])).

thf('112',plain,(
    ! [X69: $i] :
      ( ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X69 ) @ ( k2_relat_1 @ X69 ) ) ) )
      | ~ ( v1_funct_1 @ X69 )
      | ~ ( v1_relat_1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('113',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_A @ sk_D )
      = ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['111','114'])).

thf('116',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['46','49','50','51','52'])).

thf('117',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('119',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('120',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['46','49','50','51','52'])).

thf('121',plain,(
    ! [X69: $i] :
      ( ( v1_funct_2 @ X69 @ ( k1_relat_1 @ X69 ) @ ( k2_relat_1 @ X69 ) )
      | ~ ( v1_funct_1 @ X69 )
      | ~ ( v1_relat_1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('122',plain,
    ( ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('124',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','119','125','126'])).

thf('128',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['128','129'])).

thf('131',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['91','92'])).

thf('132',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('134',plain,
    ( ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( X66 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X67 )
      | ~ ( v1_funct_2 @ X67 @ X68 @ X66 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X66 ) ) )
      | ( ( k5_relat_1 @ X67 @ ( k2_funct_1 @ X67 ) )
        = ( k6_partfun1 @ X68 ) )
      | ~ ( v2_funct_1 @ X67 )
      | ( ( k2_relset_1 @ X68 @ X66 @ X67 )
       != X66 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('137',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('139',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['46','49','50','51','52'])).

thf('145',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['91','92'])).

thf('148',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('150',plain,
    ( ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference('sup+',[status(thm)],['134','150'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('152',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('153',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('154',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['151','154'])).

thf('156',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('157',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( sk_C
      = ( k4_relat_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['102','157'])).

thf('159',plain,
    ( sk_C
    = ( k4_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,
    ( ( k4_relat_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['6','159'])).

thf('161',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('164',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('166',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['164','165','166'])).

thf('168',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['161','167'])).

thf('169',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['160','168'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2VyiCdwSm2
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:10:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 3.28/3.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.28/3.48  % Solved by: fo/fo7.sh
% 3.28/3.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.28/3.48  % done 3903 iterations in 3.026s
% 3.28/3.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.28/3.48  % SZS output start Refutation
% 3.28/3.48  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.28/3.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.28/3.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.28/3.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.28/3.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.28/3.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.28/3.48  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 3.28/3.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.28/3.48  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 3.28/3.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.28/3.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.28/3.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.28/3.48  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.28/3.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.28/3.48  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.28/3.48  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.28/3.48  thf(sk_A_type, type, sk_A: $i).
% 3.28/3.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.28/3.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.28/3.48  thf(sk_D_type, type, sk_D: $i).
% 3.28/3.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.28/3.48  thf(sk_C_type, type, sk_C: $i).
% 3.28/3.48  thf(sk_B_type, type, sk_B: $i).
% 3.28/3.48  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.28/3.48  thf(t36_funct_2, conjecture,
% 3.28/3.48    (![A:$i,B:$i,C:$i]:
% 3.28/3.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.28/3.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.28/3.48       ( ![D:$i]:
% 3.28/3.48         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.28/3.48             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.28/3.48           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 3.28/3.48               ( r2_relset_1 @
% 3.28/3.48                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.28/3.48                 ( k6_partfun1 @ A ) ) & 
% 3.28/3.48               ( v2_funct_1 @ C ) ) =>
% 3.28/3.48             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.28/3.48               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 3.28/3.48  thf(zf_stmt_0, negated_conjecture,
% 3.28/3.48    (~( ![A:$i,B:$i,C:$i]:
% 3.28/3.48        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.28/3.48            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.28/3.48          ( ![D:$i]:
% 3.28/3.48            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.28/3.48                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.28/3.48              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 3.28/3.48                  ( r2_relset_1 @
% 3.28/3.48                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.28/3.48                    ( k6_partfun1 @ A ) ) & 
% 3.28/3.48                  ( v2_funct_1 @ C ) ) =>
% 3.28/3.48                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.28/3.48                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 3.28/3.48    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 3.28/3.48  thf('0', plain,
% 3.28/3.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf(cc2_relat_1, axiom,
% 3.28/3.48    (![A:$i]:
% 3.28/3.48     ( ( v1_relat_1 @ A ) =>
% 3.28/3.48       ( ![B:$i]:
% 3.28/3.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.28/3.48  thf('1', plain,
% 3.28/3.48      (![X0 : $i, X1 : $i]:
% 3.28/3.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 3.28/3.48          | (v1_relat_1 @ X0)
% 3.28/3.48          | ~ (v1_relat_1 @ X1))),
% 3.28/3.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.28/3.48  thf('2', plain,
% 3.28/3.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 3.28/3.48      inference('sup-', [status(thm)], ['0', '1'])).
% 3.28/3.48  thf(fc6_relat_1, axiom,
% 3.28/3.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.28/3.48  thf('3', plain,
% 3.28/3.48      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 3.28/3.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.28/3.48  thf('4', plain, ((v1_relat_1 @ sk_D)),
% 3.28/3.48      inference('demod', [status(thm)], ['2', '3'])).
% 3.28/3.48  thf(involutiveness_k4_relat_1, axiom,
% 3.28/3.48    (![A:$i]:
% 3.28/3.48     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 3.28/3.48  thf('5', plain,
% 3.28/3.48      (![X4 : $i]:
% 3.28/3.48         (((k4_relat_1 @ (k4_relat_1 @ X4)) = (X4)) | ~ (v1_relat_1 @ X4))),
% 3.28/3.48      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 3.28/3.48  thf('6', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 3.28/3.48      inference('sup-', [status(thm)], ['4', '5'])).
% 3.28/3.48  thf('7', plain,
% 3.28/3.48      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.28/3.48        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.28/3.48        (k6_partfun1 @ sk_A))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('8', plain,
% 3.28/3.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('9', plain,
% 3.28/3.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf(redefinition_k1_partfun1, axiom,
% 3.28/3.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.28/3.48     ( ( ( v1_funct_1 @ E ) & 
% 3.28/3.48         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.28/3.48         ( v1_funct_1 @ F ) & 
% 3.28/3.48         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.28/3.48       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.28/3.48  thf('10', plain,
% 3.28/3.48      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 3.28/3.48         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 3.28/3.48          | ~ (v1_funct_1 @ X43)
% 3.28/3.48          | ~ (v1_funct_1 @ X46)
% 3.28/3.48          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 3.28/3.48          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 3.28/3.48              = (k5_relat_1 @ X43 @ X46)))),
% 3.28/3.48      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.28/3.48  thf('11', plain,
% 3.28/3.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.28/3.48         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.28/3.48            = (k5_relat_1 @ sk_C @ X0))
% 3.28/3.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.28/3.48          | ~ (v1_funct_1 @ X0)
% 3.28/3.48          | ~ (v1_funct_1 @ sk_C))),
% 3.28/3.48      inference('sup-', [status(thm)], ['9', '10'])).
% 3.28/3.48  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('13', plain,
% 3.28/3.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.28/3.48         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.28/3.48            = (k5_relat_1 @ sk_C @ X0))
% 3.28/3.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.28/3.48          | ~ (v1_funct_1 @ X0))),
% 3.28/3.48      inference('demod', [status(thm)], ['11', '12'])).
% 3.28/3.48  thf('14', plain,
% 3.28/3.48      ((~ (v1_funct_1 @ sk_D)
% 3.28/3.48        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.28/3.48            = (k5_relat_1 @ sk_C @ sk_D)))),
% 3.28/3.48      inference('sup-', [status(thm)], ['8', '13'])).
% 3.28/3.48  thf('15', plain, ((v1_funct_1 @ sk_D)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('16', plain,
% 3.28/3.48      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.28/3.48         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.28/3.48      inference('demod', [status(thm)], ['14', '15'])).
% 3.28/3.48  thf('17', plain,
% 3.28/3.48      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.28/3.48        (k6_partfun1 @ sk_A))),
% 3.28/3.48      inference('demod', [status(thm)], ['7', '16'])).
% 3.28/3.48  thf('18', plain,
% 3.28/3.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('19', plain,
% 3.28/3.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf(dt_k1_partfun1, axiom,
% 3.28/3.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.28/3.48     ( ( ( v1_funct_1 @ E ) & 
% 3.28/3.48         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.28/3.48         ( v1_funct_1 @ F ) & 
% 3.28/3.48         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.28/3.48       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.28/3.48         ( m1_subset_1 @
% 3.28/3.48           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.28/3.48           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.28/3.48  thf('20', plain,
% 3.28/3.48      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 3.28/3.48         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 3.28/3.48          | ~ (v1_funct_1 @ X37)
% 3.28/3.48          | ~ (v1_funct_1 @ X40)
% 3.28/3.48          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 3.28/3.48          | (m1_subset_1 @ (k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40) @ 
% 3.28/3.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X42))))),
% 3.28/3.48      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.28/3.48  thf('21', plain,
% 3.28/3.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.28/3.48         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.28/3.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.28/3.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.28/3.48          | ~ (v1_funct_1 @ X1)
% 3.28/3.48          | ~ (v1_funct_1 @ sk_C))),
% 3.28/3.48      inference('sup-', [status(thm)], ['19', '20'])).
% 3.28/3.48  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('23', plain,
% 3.28/3.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.28/3.48         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.28/3.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.28/3.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.28/3.48          | ~ (v1_funct_1 @ X1))),
% 3.28/3.48      inference('demod', [status(thm)], ['21', '22'])).
% 3.28/3.48  thf('24', plain,
% 3.28/3.48      ((~ (v1_funct_1 @ sk_D)
% 3.28/3.48        | (m1_subset_1 @ 
% 3.28/3.48           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.28/3.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.28/3.48      inference('sup-', [status(thm)], ['18', '23'])).
% 3.28/3.48  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('26', plain,
% 3.28/3.48      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.28/3.48         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.28/3.48      inference('demod', [status(thm)], ['14', '15'])).
% 3.28/3.48  thf('27', plain,
% 3.28/3.48      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.28/3.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.28/3.48      inference('demod', [status(thm)], ['24', '25', '26'])).
% 3.28/3.48  thf(redefinition_r2_relset_1, axiom,
% 3.28/3.48    (![A:$i,B:$i,C:$i,D:$i]:
% 3.28/3.48     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.28/3.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.28/3.48       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.28/3.48  thf('28', plain,
% 3.28/3.48      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 3.28/3.48         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 3.28/3.48          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 3.28/3.48          | ((X32) = (X35))
% 3.28/3.48          | ~ (r2_relset_1 @ X33 @ X34 @ X32 @ X35))),
% 3.28/3.48      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.28/3.48  thf('29', plain,
% 3.28/3.48      (![X0 : $i]:
% 3.28/3.48         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 3.28/3.48          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 3.28/3.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.28/3.48      inference('sup-', [status(thm)], ['27', '28'])).
% 3.28/3.48  thf('30', plain,
% 3.28/3.48      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.28/3.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.28/3.48        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 3.28/3.48      inference('sup-', [status(thm)], ['17', '29'])).
% 3.28/3.48  thf(t29_relset_1, axiom,
% 3.28/3.48    (![A:$i]:
% 3.28/3.48     ( m1_subset_1 @
% 3.28/3.48       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.28/3.48  thf('31', plain,
% 3.28/3.48      (![X36 : $i]:
% 3.28/3.48         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 3.28/3.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 3.28/3.48      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.28/3.48  thf(redefinition_k6_partfun1, axiom,
% 3.28/3.48    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.28/3.48  thf('32', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 3.28/3.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.28/3.48  thf('33', plain,
% 3.28/3.48      (![X36 : $i]:
% 3.28/3.48         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 3.28/3.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 3.28/3.48      inference('demod', [status(thm)], ['31', '32'])).
% 3.28/3.48  thf('34', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.28/3.48      inference('demod', [status(thm)], ['30', '33'])).
% 3.28/3.48  thf(t64_funct_1, axiom,
% 3.28/3.48    (![A:$i]:
% 3.28/3.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.28/3.48       ( ![B:$i]:
% 3.28/3.48         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.28/3.48           ( ( ( v2_funct_1 @ A ) & 
% 3.28/3.48               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 3.28/3.48               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 3.28/3.48             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.28/3.48  thf('35', plain,
% 3.28/3.48      (![X24 : $i, X25 : $i]:
% 3.28/3.48         (~ (v1_relat_1 @ X24)
% 3.28/3.48          | ~ (v1_funct_1 @ X24)
% 3.28/3.48          | ((X24) = (k2_funct_1 @ X25))
% 3.28/3.48          | ((k5_relat_1 @ X24 @ X25) != (k6_relat_1 @ (k2_relat_1 @ X25)))
% 3.28/3.48          | ((k2_relat_1 @ X24) != (k1_relat_1 @ X25))
% 3.28/3.48          | ~ (v2_funct_1 @ X25)
% 3.28/3.48          | ~ (v1_funct_1 @ X25)
% 3.28/3.48          | ~ (v1_relat_1 @ X25))),
% 3.28/3.48      inference('cnf', [status(esa)], [t64_funct_1])).
% 3.28/3.48  thf('36', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 3.28/3.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.28/3.48  thf('37', plain,
% 3.28/3.48      (![X24 : $i, X25 : $i]:
% 3.28/3.48         (~ (v1_relat_1 @ X24)
% 3.28/3.48          | ~ (v1_funct_1 @ X24)
% 3.28/3.48          | ((X24) = (k2_funct_1 @ X25))
% 3.28/3.48          | ((k5_relat_1 @ X24 @ X25) != (k6_partfun1 @ (k2_relat_1 @ X25)))
% 3.28/3.48          | ((k2_relat_1 @ X24) != (k1_relat_1 @ X25))
% 3.28/3.48          | ~ (v2_funct_1 @ X25)
% 3.28/3.48          | ~ (v1_funct_1 @ X25)
% 3.28/3.48          | ~ (v1_relat_1 @ X25))),
% 3.28/3.48      inference('demod', [status(thm)], ['35', '36'])).
% 3.28/3.48  thf('38', plain,
% 3.28/3.48      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 3.28/3.48        | ~ (v1_relat_1 @ sk_D)
% 3.28/3.48        | ~ (v1_funct_1 @ sk_D)
% 3.28/3.48        | ~ (v2_funct_1 @ sk_D)
% 3.28/3.48        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 3.28/3.48        | ((sk_C) = (k2_funct_1 @ sk_D))
% 3.28/3.48        | ~ (v1_funct_1 @ sk_C)
% 3.28/3.48        | ~ (v1_relat_1 @ sk_C))),
% 3.28/3.48      inference('sup-', [status(thm)], ['34', '37'])).
% 3.28/3.48  thf('39', plain,
% 3.28/3.48      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.28/3.48        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.28/3.48        (k6_partfun1 @ sk_A))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('40', plain,
% 3.28/3.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf(t24_funct_2, axiom,
% 3.28/3.48    (![A:$i,B:$i,C:$i]:
% 3.28/3.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.28/3.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.28/3.48       ( ![D:$i]:
% 3.28/3.48         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.28/3.48             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.28/3.48           ( ( r2_relset_1 @
% 3.28/3.48               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.28/3.48               ( k6_partfun1 @ B ) ) =>
% 3.28/3.48             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.28/3.48  thf('41', plain,
% 3.28/3.48      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 3.28/3.48         (~ (v1_funct_1 @ X50)
% 3.28/3.48          | ~ (v1_funct_2 @ X50 @ X51 @ X52)
% 3.28/3.48          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 3.28/3.48          | ~ (r2_relset_1 @ X51 @ X51 @ 
% 3.28/3.48               (k1_partfun1 @ X51 @ X52 @ X52 @ X51 @ X50 @ X53) @ 
% 3.28/3.48               (k6_partfun1 @ X51))
% 3.28/3.48          | ((k2_relset_1 @ X52 @ X51 @ X53) = (X51))
% 3.28/3.48          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 3.28/3.48          | ~ (v1_funct_2 @ X53 @ X52 @ X51)
% 3.28/3.48          | ~ (v1_funct_1 @ X53))),
% 3.28/3.48      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.28/3.48  thf('42', plain,
% 3.28/3.48      (![X0 : $i]:
% 3.28/3.48         (~ (v1_funct_1 @ X0)
% 3.28/3.48          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.28/3.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.28/3.48          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.28/3.48          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.28/3.48               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.28/3.48               (k6_partfun1 @ sk_A))
% 3.28/3.48          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.28/3.48          | ~ (v1_funct_1 @ sk_C))),
% 3.28/3.48      inference('sup-', [status(thm)], ['40', '41'])).
% 3.28/3.48  thf('43', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('45', plain,
% 3.28/3.48      (![X0 : $i]:
% 3.28/3.48         (~ (v1_funct_1 @ X0)
% 3.28/3.48          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.28/3.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.28/3.48          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.28/3.48          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.28/3.48               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.28/3.48               (k6_partfun1 @ sk_A)))),
% 3.28/3.48      inference('demod', [status(thm)], ['42', '43', '44'])).
% 3.28/3.48  thf('46', plain,
% 3.28/3.48      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 3.28/3.48        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.28/3.48        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.28/3.48        | ~ (v1_funct_1 @ sk_D))),
% 3.28/3.48      inference('sup-', [status(thm)], ['39', '45'])).
% 3.28/3.48  thf('47', plain,
% 3.28/3.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf(redefinition_k2_relset_1, axiom,
% 3.28/3.48    (![A:$i,B:$i,C:$i]:
% 3.28/3.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.28/3.48       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.28/3.48  thf('48', plain,
% 3.28/3.48      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.28/3.48         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 3.28/3.48          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 3.28/3.48      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.28/3.48  thf('49', plain,
% 3.28/3.48      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.28/3.48      inference('sup-', [status(thm)], ['47', '48'])).
% 3.28/3.48  thf('50', plain,
% 3.28/3.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('51', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('53', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.28/3.48      inference('demod', [status(thm)], ['46', '49', '50', '51', '52'])).
% 3.28/3.48  thf('54', plain, ((v1_relat_1 @ sk_D)),
% 3.28/3.48      inference('demod', [status(thm)], ['2', '3'])).
% 3.28/3.48  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('56', plain,
% 3.28/3.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('57', plain,
% 3.28/3.48      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.28/3.48         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 3.28/3.48          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 3.28/3.48      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.28/3.48  thf('58', plain,
% 3.28/3.48      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 3.28/3.48      inference('sup-', [status(thm)], ['56', '57'])).
% 3.28/3.48  thf('59', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('60', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.28/3.48      inference('sup+', [status(thm)], ['58', '59'])).
% 3.28/3.48  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('62', plain,
% 3.28/3.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('63', plain,
% 3.28/3.48      (![X0 : $i, X1 : $i]:
% 3.28/3.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 3.28/3.48          | (v1_relat_1 @ X0)
% 3.28/3.48          | ~ (v1_relat_1 @ X1))),
% 3.28/3.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.28/3.48  thf('64', plain,
% 3.28/3.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 3.28/3.48      inference('sup-', [status(thm)], ['62', '63'])).
% 3.28/3.48  thf('65', plain,
% 3.28/3.48      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 3.28/3.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.28/3.48  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 3.28/3.48      inference('demod', [status(thm)], ['64', '65'])).
% 3.28/3.48  thf('67', plain,
% 3.28/3.48      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 3.28/3.48        | ~ (v2_funct_1 @ sk_D)
% 3.28/3.48        | ((sk_B) != (k1_relat_1 @ sk_D))
% 3.28/3.48        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 3.28/3.48      inference('demod', [status(thm)],
% 3.28/3.48                ['38', '53', '54', '55', '60', '61', '66'])).
% 3.28/3.48  thf('68', plain,
% 3.28/3.48      ((((sk_C) = (k2_funct_1 @ sk_D))
% 3.28/3.48        | ((sk_B) != (k1_relat_1 @ sk_D))
% 3.28/3.48        | ~ (v2_funct_1 @ sk_D))),
% 3.28/3.48      inference('simplify', [status(thm)], ['67'])).
% 3.28/3.48  thf('69', plain,
% 3.28/3.48      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.28/3.48         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.28/3.48      inference('demod', [status(thm)], ['14', '15'])).
% 3.28/3.48  thf('70', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.28/3.48      inference('demod', [status(thm)], ['30', '33'])).
% 3.28/3.48  thf('71', plain,
% 3.28/3.48      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.28/3.48         = (k6_partfun1 @ sk_A))),
% 3.28/3.48      inference('demod', [status(thm)], ['69', '70'])).
% 3.28/3.48  thf('72', plain,
% 3.28/3.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf(t30_funct_2, axiom,
% 3.28/3.48    (![A:$i,B:$i,C:$i,D:$i]:
% 3.28/3.48     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.28/3.48         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 3.28/3.48       ( ![E:$i]:
% 3.28/3.48         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 3.28/3.48             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 3.28/3.48           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 3.28/3.48               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 3.28/3.48             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 3.28/3.48               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 3.28/3.48  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 3.28/3.48  thf(zf_stmt_2, axiom,
% 3.28/3.48    (![C:$i,B:$i]:
% 3.28/3.48     ( ( zip_tseitin_1 @ C @ B ) =>
% 3.28/3.48       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 3.28/3.48  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 3.28/3.48  thf(zf_stmt_4, axiom,
% 3.28/3.48    (![E:$i,D:$i]:
% 3.28/3.48     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 3.28/3.48  thf(zf_stmt_5, axiom,
% 3.28/3.48    (![A:$i,B:$i,C:$i,D:$i]:
% 3.28/3.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.28/3.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.28/3.48       ( ![E:$i]:
% 3.28/3.48         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.28/3.48             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.28/3.48           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 3.28/3.48               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 3.28/3.48             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 3.28/3.48  thf('73', plain,
% 3.28/3.48      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 3.28/3.48         (~ (v1_funct_1 @ X58)
% 3.28/3.48          | ~ (v1_funct_2 @ X58 @ X59 @ X60)
% 3.28/3.48          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60)))
% 3.28/3.48          | (zip_tseitin_0 @ X58 @ X61)
% 3.28/3.48          | ~ (v2_funct_1 @ (k1_partfun1 @ X62 @ X59 @ X59 @ X60 @ X61 @ X58))
% 3.28/3.48          | (zip_tseitin_1 @ X60 @ X59)
% 3.28/3.48          | ((k2_relset_1 @ X62 @ X59 @ X61) != (X59))
% 3.28/3.48          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X59)))
% 3.28/3.48          | ~ (v1_funct_2 @ X61 @ X62 @ X59)
% 3.28/3.48          | ~ (v1_funct_1 @ X61))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.28/3.48  thf('74', plain,
% 3.28/3.48      (![X0 : $i, X1 : $i]:
% 3.28/3.48         (~ (v1_funct_1 @ X0)
% 3.28/3.48          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.28/3.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.28/3.48          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 3.28/3.48          | (zip_tseitin_1 @ sk_A @ sk_B)
% 3.28/3.48          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.28/3.48          | (zip_tseitin_0 @ sk_D @ X0)
% 3.28/3.48          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.28/3.48          | ~ (v1_funct_1 @ sk_D))),
% 3.28/3.48      inference('sup-', [status(thm)], ['72', '73'])).
% 3.28/3.48  thf('75', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('77', plain,
% 3.28/3.48      (![X0 : $i, X1 : $i]:
% 3.28/3.48         (~ (v1_funct_1 @ X0)
% 3.28/3.48          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.28/3.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.28/3.48          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 3.28/3.48          | (zip_tseitin_1 @ sk_A @ sk_B)
% 3.28/3.48          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.28/3.48          | (zip_tseitin_0 @ sk_D @ X0))),
% 3.28/3.48      inference('demod', [status(thm)], ['74', '75', '76'])).
% 3.28/3.48  thf('78', plain,
% 3.28/3.48      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 3.28/3.48        | (zip_tseitin_0 @ sk_D @ sk_C)
% 3.28/3.48        | (zip_tseitin_1 @ sk_A @ sk_B)
% 3.28/3.48        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 3.28/3.48        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.28/3.48        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.28/3.48        | ~ (v1_funct_1 @ sk_C))),
% 3.28/3.48      inference('sup-', [status(thm)], ['71', '77'])).
% 3.28/3.48  thf(fc4_funct_1, axiom,
% 3.28/3.48    (![A:$i]:
% 3.28/3.48     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.28/3.48       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.28/3.48  thf('79', plain, (![X17 : $i]: (v2_funct_1 @ (k6_relat_1 @ X17))),
% 3.28/3.48      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.28/3.48  thf('80', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 3.28/3.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.28/3.48  thf('81', plain, (![X17 : $i]: (v2_funct_1 @ (k6_partfun1 @ X17))),
% 3.28/3.48      inference('demod', [status(thm)], ['79', '80'])).
% 3.28/3.48  thf('82', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('83', plain,
% 3.28/3.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('84', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('86', plain,
% 3.28/3.48      (((zip_tseitin_0 @ sk_D @ sk_C)
% 3.28/3.48        | (zip_tseitin_1 @ sk_A @ sk_B)
% 3.28/3.48        | ((sk_B) != (sk_B)))),
% 3.28/3.48      inference('demod', [status(thm)], ['78', '81', '82', '83', '84', '85'])).
% 3.28/3.48  thf('87', plain,
% 3.28/3.48      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 3.28/3.48      inference('simplify', [status(thm)], ['86'])).
% 3.28/3.48  thf('88', plain,
% 3.28/3.48      (![X56 : $i, X57 : $i]:
% 3.28/3.48         (((X56) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X56 @ X57))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.28/3.48  thf('89', plain,
% 3.28/3.48      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.28/3.48      inference('sup-', [status(thm)], ['87', '88'])).
% 3.28/3.48  thf('90', plain, (((sk_A) != (k1_xboole_0))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('91', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 3.28/3.48      inference('simplify_reflect-', [status(thm)], ['89', '90'])).
% 3.28/3.48  thf('92', plain,
% 3.28/3.48      (![X54 : $i, X55 : $i]:
% 3.28/3.48         ((v2_funct_1 @ X55) | ~ (zip_tseitin_0 @ X55 @ X54))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.28/3.48  thf('93', plain, ((v2_funct_1 @ sk_D)),
% 3.28/3.48      inference('sup-', [status(thm)], ['91', '92'])).
% 3.28/3.48  thf('94', plain,
% 3.28/3.48      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 3.28/3.48      inference('demod', [status(thm)], ['68', '93'])).
% 3.28/3.48  thf('95', plain, ((v1_funct_1 @ sk_D)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf(d9_funct_1, axiom,
% 3.28/3.48    (![A:$i]:
% 3.28/3.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.28/3.48       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 3.28/3.48  thf('96', plain,
% 3.28/3.48      (![X12 : $i]:
% 3.28/3.48         (~ (v2_funct_1 @ X12)
% 3.28/3.48          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 3.28/3.48          | ~ (v1_funct_1 @ X12)
% 3.28/3.48          | ~ (v1_relat_1 @ X12))),
% 3.28/3.48      inference('cnf', [status(esa)], [d9_funct_1])).
% 3.28/3.48  thf('97', plain,
% 3.28/3.48      ((~ (v1_relat_1 @ sk_D)
% 3.28/3.48        | ((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))
% 3.28/3.48        | ~ (v2_funct_1 @ sk_D))),
% 3.28/3.48      inference('sup-', [status(thm)], ['95', '96'])).
% 3.28/3.48  thf('98', plain, ((v1_relat_1 @ sk_D)),
% 3.28/3.48      inference('demod', [status(thm)], ['2', '3'])).
% 3.28/3.48  thf('99', plain,
% 3.28/3.48      ((((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 3.28/3.48      inference('demod', [status(thm)], ['97', '98'])).
% 3.28/3.48  thf('100', plain, ((v2_funct_1 @ sk_D)),
% 3.28/3.48      inference('sup-', [status(thm)], ['91', '92'])).
% 3.28/3.48  thf('101', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 3.28/3.48      inference('demod', [status(thm)], ['99', '100'])).
% 3.28/3.48  thf('102', plain,
% 3.28/3.48      ((((sk_C) = (k4_relat_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 3.28/3.48      inference('demod', [status(thm)], ['94', '101'])).
% 3.28/3.48  thf('103', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.28/3.48      inference('demod', [status(thm)], ['46', '49', '50', '51', '52'])).
% 3.28/3.48  thf(t3_funct_2, axiom,
% 3.28/3.48    (![A:$i]:
% 3.28/3.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.28/3.48       ( ( v1_funct_1 @ A ) & 
% 3.28/3.48         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 3.28/3.48         ( m1_subset_1 @
% 3.28/3.48           A @ 
% 3.28/3.48           ( k1_zfmisc_1 @
% 3.28/3.48             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 3.28/3.48  thf('104', plain,
% 3.28/3.48      (![X69 : $i]:
% 3.28/3.48         ((m1_subset_1 @ X69 @ 
% 3.28/3.48           (k1_zfmisc_1 @ 
% 3.28/3.48            (k2_zfmisc_1 @ (k1_relat_1 @ X69) @ (k2_relat_1 @ X69))))
% 3.28/3.48          | ~ (v1_funct_1 @ X69)
% 3.28/3.48          | ~ (v1_relat_1 @ X69))),
% 3.28/3.48      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.28/3.48  thf('105', plain,
% 3.28/3.48      (((m1_subset_1 @ sk_D @ 
% 3.28/3.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_A)))
% 3.28/3.48        | ~ (v1_relat_1 @ sk_D)
% 3.28/3.48        | ~ (v1_funct_1 @ sk_D))),
% 3.28/3.48      inference('sup+', [status(thm)], ['103', '104'])).
% 3.28/3.48  thf('106', plain, ((v1_relat_1 @ sk_D)),
% 3.28/3.48      inference('demod', [status(thm)], ['2', '3'])).
% 3.28/3.48  thf('107', plain, ((v1_funct_1 @ sk_D)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('108', plain,
% 3.28/3.48      ((m1_subset_1 @ sk_D @ 
% 3.28/3.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_A)))),
% 3.28/3.48      inference('demod', [status(thm)], ['105', '106', '107'])).
% 3.28/3.48  thf(t35_funct_2, axiom,
% 3.28/3.48    (![A:$i,B:$i,C:$i]:
% 3.28/3.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.28/3.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.28/3.48       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 3.28/3.48         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.28/3.48           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 3.28/3.48             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 3.28/3.48  thf('109', plain,
% 3.28/3.48      (![X66 : $i, X67 : $i, X68 : $i]:
% 3.28/3.48         (((X66) = (k1_xboole_0))
% 3.28/3.48          | ~ (v1_funct_1 @ X67)
% 3.28/3.48          | ~ (v1_funct_2 @ X67 @ X68 @ X66)
% 3.28/3.48          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X66)))
% 3.28/3.48          | ((k5_relat_1 @ X67 @ (k2_funct_1 @ X67)) = (k6_partfun1 @ X68))
% 3.28/3.48          | ~ (v2_funct_1 @ X67)
% 3.28/3.48          | ((k2_relset_1 @ X68 @ X66 @ X67) != (X66)))),
% 3.28/3.48      inference('cnf', [status(esa)], [t35_funct_2])).
% 3.28/3.48  thf('110', plain,
% 3.28/3.48      ((((k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_A @ sk_D) != (sk_A))
% 3.28/3.48        | ~ (v2_funct_1 @ sk_D)
% 3.28/3.48        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D))
% 3.28/3.48            = (k6_partfun1 @ (k1_relat_1 @ sk_D)))
% 3.28/3.48        | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_A)
% 3.28/3.48        | ~ (v1_funct_1 @ sk_D)
% 3.28/3.48        | ((sk_A) = (k1_xboole_0)))),
% 3.28/3.48      inference('sup-', [status(thm)], ['108', '109'])).
% 3.28/3.48  thf('111', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.28/3.48      inference('demod', [status(thm)], ['46', '49', '50', '51', '52'])).
% 3.28/3.48  thf('112', plain,
% 3.28/3.48      (![X69 : $i]:
% 3.28/3.48         ((m1_subset_1 @ X69 @ 
% 3.28/3.48           (k1_zfmisc_1 @ 
% 3.28/3.48            (k2_zfmisc_1 @ (k1_relat_1 @ X69) @ (k2_relat_1 @ X69))))
% 3.28/3.48          | ~ (v1_funct_1 @ X69)
% 3.28/3.48          | ~ (v1_relat_1 @ X69))),
% 3.28/3.48      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.28/3.48  thf('113', plain,
% 3.28/3.48      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.28/3.48         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 3.28/3.48          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 3.28/3.48      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.28/3.48  thf('114', plain,
% 3.28/3.48      (![X0 : $i]:
% 3.28/3.48         (~ (v1_relat_1 @ X0)
% 3.28/3.48          | ~ (v1_funct_1 @ X0)
% 3.28/3.48          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 3.28/3.48              = (k2_relat_1 @ X0)))),
% 3.28/3.48      inference('sup-', [status(thm)], ['112', '113'])).
% 3.28/3.48  thf('115', plain,
% 3.28/3.48      ((((k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_A @ sk_D)
% 3.28/3.48          = (k2_relat_1 @ sk_D))
% 3.28/3.48        | ~ (v1_funct_1 @ sk_D)
% 3.28/3.48        | ~ (v1_relat_1 @ sk_D))),
% 3.28/3.48      inference('sup+', [status(thm)], ['111', '114'])).
% 3.28/3.48  thf('116', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.28/3.48      inference('demod', [status(thm)], ['46', '49', '50', '51', '52'])).
% 3.28/3.48  thf('117', plain, ((v1_funct_1 @ sk_D)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('118', plain, ((v1_relat_1 @ sk_D)),
% 3.28/3.48      inference('demod', [status(thm)], ['2', '3'])).
% 3.28/3.48  thf('119', plain,
% 3.28/3.48      (((k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_A @ sk_D) = (sk_A))),
% 3.28/3.48      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 3.28/3.48  thf('120', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.28/3.48      inference('demod', [status(thm)], ['46', '49', '50', '51', '52'])).
% 3.28/3.48  thf('121', plain,
% 3.28/3.48      (![X69 : $i]:
% 3.28/3.48         ((v1_funct_2 @ X69 @ (k1_relat_1 @ X69) @ (k2_relat_1 @ X69))
% 3.28/3.48          | ~ (v1_funct_1 @ X69)
% 3.28/3.48          | ~ (v1_relat_1 @ X69))),
% 3.28/3.48      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.28/3.48  thf('122', plain,
% 3.28/3.48      (((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_A)
% 3.28/3.48        | ~ (v1_relat_1 @ sk_D)
% 3.28/3.48        | ~ (v1_funct_1 @ sk_D))),
% 3.28/3.48      inference('sup+', [status(thm)], ['120', '121'])).
% 3.28/3.48  thf('123', plain, ((v1_relat_1 @ sk_D)),
% 3.28/3.48      inference('demod', [status(thm)], ['2', '3'])).
% 3.28/3.48  thf('124', plain, ((v1_funct_1 @ sk_D)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('125', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_A)),
% 3.28/3.48      inference('demod', [status(thm)], ['122', '123', '124'])).
% 3.28/3.48  thf('126', plain, ((v1_funct_1 @ sk_D)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('127', plain,
% 3.28/3.48      ((((sk_A) != (sk_A))
% 3.28/3.48        | ~ (v2_funct_1 @ sk_D)
% 3.28/3.48        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D))
% 3.28/3.48            = (k6_partfun1 @ (k1_relat_1 @ sk_D)))
% 3.28/3.48        | ((sk_A) = (k1_xboole_0)))),
% 3.28/3.48      inference('demod', [status(thm)], ['110', '119', '125', '126'])).
% 3.28/3.48  thf('128', plain,
% 3.28/3.48      ((((sk_A) = (k1_xboole_0))
% 3.28/3.48        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D))
% 3.28/3.48            = (k6_partfun1 @ (k1_relat_1 @ sk_D)))
% 3.28/3.48        | ~ (v2_funct_1 @ sk_D))),
% 3.28/3.48      inference('simplify', [status(thm)], ['127'])).
% 3.28/3.48  thf('129', plain, (((sk_A) != (k1_xboole_0))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('130', plain,
% 3.28/3.48      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D))
% 3.28/3.48          = (k6_partfun1 @ (k1_relat_1 @ sk_D)))
% 3.28/3.48        | ~ (v2_funct_1 @ sk_D))),
% 3.28/3.48      inference('simplify_reflect-', [status(thm)], ['128', '129'])).
% 3.28/3.48  thf('131', plain, ((v2_funct_1 @ sk_D)),
% 3.28/3.48      inference('sup-', [status(thm)], ['91', '92'])).
% 3.28/3.48  thf('132', plain,
% 3.28/3.48      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D))
% 3.28/3.48         = (k6_partfun1 @ (k1_relat_1 @ sk_D)))),
% 3.28/3.48      inference('demod', [status(thm)], ['130', '131'])).
% 3.28/3.48  thf('133', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 3.28/3.48      inference('demod', [status(thm)], ['99', '100'])).
% 3.28/3.48  thf('134', plain,
% 3.28/3.48      (((k5_relat_1 @ sk_D @ (k4_relat_1 @ sk_D))
% 3.28/3.48         = (k6_partfun1 @ (k1_relat_1 @ sk_D)))),
% 3.28/3.48      inference('demod', [status(thm)], ['132', '133'])).
% 3.28/3.48  thf('135', plain,
% 3.28/3.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('136', plain,
% 3.28/3.48      (![X66 : $i, X67 : $i, X68 : $i]:
% 3.28/3.48         (((X66) = (k1_xboole_0))
% 3.28/3.48          | ~ (v1_funct_1 @ X67)
% 3.28/3.48          | ~ (v1_funct_2 @ X67 @ X68 @ X66)
% 3.28/3.48          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X66)))
% 3.28/3.48          | ((k5_relat_1 @ X67 @ (k2_funct_1 @ X67)) = (k6_partfun1 @ X68))
% 3.28/3.48          | ~ (v2_funct_1 @ X67)
% 3.28/3.48          | ((k2_relset_1 @ X68 @ X66 @ X67) != (X66)))),
% 3.28/3.48      inference('cnf', [status(esa)], [t35_funct_2])).
% 3.28/3.48  thf('137', plain,
% 3.28/3.48      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 3.28/3.48        | ~ (v2_funct_1 @ sk_D)
% 3.28/3.48        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 3.28/3.48        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.28/3.48        | ~ (v1_funct_1 @ sk_D)
% 3.28/3.48        | ((sk_A) = (k1_xboole_0)))),
% 3.28/3.48      inference('sup-', [status(thm)], ['135', '136'])).
% 3.28/3.48  thf('138', plain,
% 3.28/3.48      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.28/3.48      inference('sup-', [status(thm)], ['47', '48'])).
% 3.28/3.48  thf('139', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('140', plain, ((v1_funct_1 @ sk_D)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('141', plain,
% 3.28/3.48      ((((k2_relat_1 @ sk_D) != (sk_A))
% 3.28/3.48        | ~ (v2_funct_1 @ sk_D)
% 3.28/3.48        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 3.28/3.48        | ((sk_A) = (k1_xboole_0)))),
% 3.28/3.48      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 3.28/3.48  thf('142', plain, (((sk_A) != (k1_xboole_0))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('143', plain,
% 3.28/3.48      ((((k2_relat_1 @ sk_D) != (sk_A))
% 3.28/3.48        | ~ (v2_funct_1 @ sk_D)
% 3.28/3.48        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 3.28/3.48      inference('simplify_reflect-', [status(thm)], ['141', '142'])).
% 3.28/3.48  thf('144', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.28/3.48      inference('demod', [status(thm)], ['46', '49', '50', '51', '52'])).
% 3.28/3.48  thf('145', plain,
% 3.28/3.48      ((((sk_A) != (sk_A))
% 3.28/3.48        | ~ (v2_funct_1 @ sk_D)
% 3.28/3.48        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 3.28/3.48      inference('demod', [status(thm)], ['143', '144'])).
% 3.28/3.48  thf('146', plain,
% 3.28/3.48      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 3.28/3.48        | ~ (v2_funct_1 @ sk_D))),
% 3.28/3.48      inference('simplify', [status(thm)], ['145'])).
% 3.28/3.48  thf('147', plain, ((v2_funct_1 @ sk_D)),
% 3.28/3.48      inference('sup-', [status(thm)], ['91', '92'])).
% 3.28/3.48  thf('148', plain,
% 3.28/3.48      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 3.28/3.48      inference('demod', [status(thm)], ['146', '147'])).
% 3.28/3.48  thf('149', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 3.28/3.48      inference('demod', [status(thm)], ['99', '100'])).
% 3.28/3.48  thf('150', plain,
% 3.28/3.48      (((k5_relat_1 @ sk_D @ (k4_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 3.28/3.48      inference('demod', [status(thm)], ['148', '149'])).
% 3.28/3.48  thf('151', plain,
% 3.28/3.48      (((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 3.28/3.48      inference('sup+', [status(thm)], ['134', '150'])).
% 3.28/3.48  thf(t71_relat_1, axiom,
% 3.28/3.48    (![A:$i]:
% 3.28/3.48     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.28/3.48       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.28/3.48  thf('152', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 3.28/3.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.28/3.48  thf('153', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 3.28/3.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.28/3.48  thf('154', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 3.28/3.48      inference('demod', [status(thm)], ['152', '153'])).
% 3.28/3.48  thf('155', plain,
% 3.28/3.48      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 3.28/3.48      inference('sup+', [status(thm)], ['151', '154'])).
% 3.28/3.48  thf('156', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 3.28/3.48      inference('demod', [status(thm)], ['152', '153'])).
% 3.28/3.48  thf('157', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 3.28/3.48      inference('demod', [status(thm)], ['155', '156'])).
% 3.28/3.48  thf('158', plain, ((((sk_C) = (k4_relat_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 3.28/3.48      inference('demod', [status(thm)], ['102', '157'])).
% 3.28/3.48  thf('159', plain, (((sk_C) = (k4_relat_1 @ sk_D))),
% 3.28/3.48      inference('simplify', [status(thm)], ['158'])).
% 3.28/3.48  thf('160', plain, (((k4_relat_1 @ sk_C) = (sk_D))),
% 3.28/3.48      inference('demod', [status(thm)], ['6', '159'])).
% 3.28/3.48  thf('161', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('162', plain, ((v1_funct_1 @ sk_C)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('163', plain,
% 3.28/3.48      (![X12 : $i]:
% 3.28/3.48         (~ (v2_funct_1 @ X12)
% 3.28/3.48          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 3.28/3.48          | ~ (v1_funct_1 @ X12)
% 3.28/3.48          | ~ (v1_relat_1 @ X12))),
% 3.28/3.48      inference('cnf', [status(esa)], [d9_funct_1])).
% 3.28/3.48  thf('164', plain,
% 3.28/3.48      ((~ (v1_relat_1 @ sk_C)
% 3.28/3.48        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 3.28/3.48        | ~ (v2_funct_1 @ sk_C))),
% 3.28/3.48      inference('sup-', [status(thm)], ['162', '163'])).
% 3.28/3.48  thf('165', plain, ((v1_relat_1 @ sk_C)),
% 3.28/3.48      inference('demod', [status(thm)], ['64', '65'])).
% 3.28/3.48  thf('166', plain, ((v2_funct_1 @ sk_C)),
% 3.28/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.28/3.48  thf('167', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 3.28/3.48      inference('demod', [status(thm)], ['164', '165', '166'])).
% 3.28/3.48  thf('168', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 3.28/3.48      inference('demod', [status(thm)], ['161', '167'])).
% 3.28/3.48  thf('169', plain, ($false),
% 3.28/3.48      inference('simplify_reflect-', [status(thm)], ['160', '168'])).
% 3.28/3.48  
% 3.28/3.48  % SZS output end Refutation
% 3.28/3.48  
% 3.28/3.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
