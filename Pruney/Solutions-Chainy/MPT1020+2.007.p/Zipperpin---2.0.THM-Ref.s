%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wAOgbck9Tq

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:01 EST 2020

% Result     : Theorem 16.45s
% Output     : Refutation 16.45s
% Verified   : 
% Statistics : Number of formulae       :  289 (5030 expanded)
%              Number of leaves         :   63 (1515 expanded)
%              Depth                    :   21
%              Number of atoms          : 2362 (121111 expanded)
%              Number of equality atoms :  159 (1410 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(t87_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( v3_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( v3_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X85: $i,X86: $i] :
      ( ( ( k2_funct_2 @ X86 @ X85 )
        = ( k2_funct_1 @ X85 ) )
      | ~ ( m1_subset_1 @ X85 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X86 @ X86 ) ) )
      | ~ ( v3_funct_2 @ X85 @ X86 @ X86 )
      | ~ ( v1_funct_2 @ X85 @ X86 @ X86 )
      | ~ ( v1_funct_1 @ X85 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X87: $i] :
      ( ( k6_partfun1 @ X87 )
      = ( k6_relat_1 @ X87 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1 ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ! [X79: $i,X80: $i,X81: $i,X82: $i,X83: $i,X84: $i] :
      ( ~ ( m1_subset_1 @ X79 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X80 @ X81 ) ) )
      | ~ ( v1_funct_1 @ X79 )
      | ~ ( v1_funct_1 @ X82 )
      | ~ ( m1_subset_1 @ X82 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X83 @ X84 ) ) )
      | ( ( k1_partfun1 @ X80 @ X81 @ X83 @ X84 @ X79 @ X82 )
        = ( k5_relat_1 @ X79 @ X82 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1 )
      = ( k5_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1 )
    = ( k5_relat_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C_1 ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ! [X69: $i,X70: $i,X71: $i,X72: $i,X73: $i,X74: $i] :
      ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X70 @ X71 ) ) )
      | ~ ( v1_funct_1 @ X69 )
      | ~ ( v1_funct_1 @ X72 )
      | ~ ( m1_subset_1 @ X72 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X73 @ X74 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X70 @ X71 @ X73 @ X74 @ X69 @ X72 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X70 @ X74 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1 )
    = ( k5_relat_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('31',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('32',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( X45 = X48 )
      | ~ ( r2_relset_1 @ X46 @ X47 @ X45 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C_1 ) @ X0 )
      | ( ( k5_relat_1 @ sk_B @ sk_C_1 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_B @ sk_C_1 )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','33'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('35',plain,(
    ! [X78: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X78 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X78 @ X78 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('36',plain,(
    ! [X87: $i] :
      ( ( k6_partfun1 @ X87 )
      = ( k6_relat_1 @ X87 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('37',plain,(
    ! [X78: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X78 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X78 @ X78 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C_1 )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('40',plain,(
    ! [X88: $i,X89: $i,X90: $i] :
      ( ( X88 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X89 )
      | ~ ( v1_funct_2 @ X89 @ X90 @ X88 )
      | ~ ( m1_subset_1 @ X89 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X90 @ X88 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X89 ) @ X89 )
        = ( k6_partfun1 @ X88 ) )
      | ~ ( v2_funct_1 @ X89 )
      | ( ( k2_relset_1 @ X90 @ X88 @ X89 )
       != X88 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('41',plain,(
    ! [X87: $i] :
      ( ( k6_partfun1 @ X87 )
      = ( k6_relat_1 @ X87 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('42',plain,(
    ! [X88: $i,X89: $i,X90: $i] :
      ( ( X88 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X89 )
      | ~ ( v1_funct_2 @ X89 @ X90 @ X88 )
      | ~ ( m1_subset_1 @ X89 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X90 @ X88 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X89 ) @ X89 )
        = ( k6_relat_1 @ X88 ) )
      | ~ ( v2_funct_1 @ X89 )
      | ( ( k2_relset_1 @ X90 @ X88 @ X89 )
       != X88 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('45',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k7_relset_1 @ X50 @ X51 @ X52 @ X50 )
        = ( k2_relset_1 @ X50 @ X51 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('46',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_B @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('48',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k7_relset_1 @ X42 @ X43 @ X41 @ X44 )
        = ( k9_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_B @ X0 )
      = ( k9_relat_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v4_relat_1 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22
        = ( k7_relat_1 @ X22 @ X23 ) )
      | ~ ( v4_relat_1 @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_B
      = ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('59',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('60',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( sk_B
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('63',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k9_relat_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k2_relset_1 @ sk_A @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['50','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('68',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( v1_funct_1 @ X56 )
      | ~ ( v3_funct_2 @ X56 @ X57 @ X58 )
      | ( v2_funct_2 @ X56 @ X58 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('69',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['69','70','71'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('73',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( v2_funct_2 @ X68 @ X67 )
      | ( ( k2_relat_1 @ X68 )
        = X67 )
      | ~ ( v5_relat_1 @ X68 @ X67 )
      | ~ ( v1_relat_1 @ X68 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v5_relat_1 @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('78',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['74','75','78'])).

thf('80',plain,
    ( sk_A
    = ( k2_relset_1 @ sk_A @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['66','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( v1_funct_1 @ X56 )
      | ~ ( v3_funct_2 @ X56 @ X57 @ X58 )
      | ( v2_funct_1 @ X56 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('83',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( sk_A != sk_A )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','80','86','87','88'])).

thf('90',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('91',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k5_relat_1 @ X25 @ ( k5_relat_1 @ X24 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k5_relat_1 @ sk_B @ X0 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) )
        & ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( m1_subset_1 @ ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) )).

thf('94',plain,(
    ! [X75: $i,X76: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X75 @ X76 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X75 @ X75 ) ) )
      | ~ ( m1_subset_1 @ X76 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X75 @ X75 ) ) )
      | ~ ( v3_funct_2 @ X76 @ X75 @ X75 )
      | ~ ( v1_funct_2 @ X76 @ X75 @ X75 )
      | ~ ( v1_funct_1 @ X76 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('95',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('100',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_relat_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('101',plain,(
    v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('103',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k5_relat_1 @ sk_B @ X0 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','103','104'])).

thf('106',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C_1 )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','105'])).

thf('107',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_A ),
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

thf('108',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( v1_funct_2 @ X63 @ X61 @ X62 )
      | ( X61
        = ( k1_relset_1 @ X61 @ X62 @ X63 ) )
      | ~ ( zip_tseitin_1 @ X63 @ X62 @ X61 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('109',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('111',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k1_relset_1 @ X39 @ X40 @ X38 )
        = ( k1_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('112',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['109','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('115',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( zip_tseitin_0 @ X64 @ X65 )
      | ( zip_tseitin_1 @ X66 @ X64 @ X65 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X64 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('116',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X59: $i,X60: $i] :
      ( ( zip_tseitin_0 @ X59 @ X60 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('118',plain,(
    ! [X59: $i,X60: $i] :
      ( ( zip_tseitin_0 @ X59 @ X60 )
      | ( X60 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('119',plain,(
    ! [X59: $i] :
      ( zip_tseitin_0 @ X59 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['117','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['120'])).

thf('122',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['116','121'])).

thf('123',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['113','122'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('124',plain,(
    ! [X28: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X28 ) ) @ X28 )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('125',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C_1 )
      = sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('128',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('130',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['125','130'])).

thf('132',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('133',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( v1_funct_1 @ X56 )
      | ~ ( v3_funct_2 @ X56 @ X57 @ X58 )
      | ( v2_funct_2 @ X56 @ X58 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('134',plain,
    ( ( v2_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X75: $i,X76: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X75 @ X76 ) @ X75 @ X75 )
      | ~ ( m1_subset_1 @ X76 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X75 @ X75 ) ) )
      | ~ ( v3_funct_2 @ X76 @ X75 @ X75 )
      | ~ ( v1_funct_2 @ X76 @ X75 @ X75 )
      | ~ ( v1_funct_1 @ X76 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('137',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X75: $i,X76: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X75 @ X76 ) )
      | ~ ( m1_subset_1 @ X76 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X75 @ X75 ) ) )
      | ~ ( v3_funct_2 @ X76 @ X75 @ X75 )
      | ~ ( v1_funct_2 @ X76 @ X75 @ X75 )
      | ~ ( v1_funct_1 @ X76 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('144',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['144','145','146','147'])).

thf('149',plain,(
    v2_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['134','141','148'])).

thf('150',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( v2_funct_2 @ X68 @ X67 )
      | ( ( k2_relat_1 @ X68 )
        = X67 )
      | ~ ( v5_relat_1 @ X68 @ X67 )
      | ~ ( v1_relat_1 @ X68 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('151',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) )
    | ~ ( v5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('153',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('154',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v5_relat_1 @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('155',plain,(
    v5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( k2_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['151','152','155'])).

thf('157',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('158',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['156','157'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('159',plain,(
    ! [X29: $i] :
      ( ( ( k5_relat_1 @ X29 @ ( k6_relat_1 @ ( k2_relat_1 @ X29 ) ) )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('160',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
      = ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('162',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['128','129'])).

thf('164',plain,
    ( ( sk_C_1
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','131','162','163'])).

thf('165',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('166',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( r2_relset_1 @ X46 @ X47 @ X45 @ X48 )
      | ( X45 != X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('169',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( r2_relset_1 @ X46 @ X47 @ X48 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['167','169'])).

thf('171',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['166','170'])).

thf('172',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['166','170'])).

thf('173',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','171','172'])).

thf('174',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['113','122'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('175',plain,(
    ! [X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('176',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['128','129'])).

thf('178',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['166','170'])).

thf('180',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( v1_funct_2 @ X63 @ X61 @ X62 )
      | ( X61
        = ( k1_relset_1 @ X61 @ X62 @ X63 ) )
      | ~ ( zip_tseitin_1 @ X63 @ X62 @ X61 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('184',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k1_relset_1 @ X39 @ X40 @ X38 )
        = ( k1_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('187',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['184','187'])).

thf('189',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( zip_tseitin_0 @ X64 @ X65 )
      | ( zip_tseitin_1 @ X66 @ X64 @ X65 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X64 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('191',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['120'])).

thf('193',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['188','193'])).

thf('195',plain,(
    ! [X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('196',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('198',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['166','170'])).

thf('200',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,
    ( ( k2_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['151','152','155'])).

thf('203',plain,(
    ! [X27: $i] :
      ( ( ( k2_relat_1 @ X27 )
       != k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('204',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('206',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('208',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['166','170'])).

thf('210',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,
    ( ( k2_funct_1 @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['200'])).

thf('213',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['173','181','201','213'])).

thf('215',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( r2_relset_1 @ X46 @ X47 @ X48 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('217',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['166','170'])).

thf('219',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['166','170'])).

thf('220',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['200'])).

thf('222',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['200'])).

thf('223',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('224',plain,(
    $false ),
    inference(demod,[status(thm)],['214','223'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wAOgbck9Tq
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:59:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 16.45/16.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 16.45/16.65  % Solved by: fo/fo7.sh
% 16.45/16.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 16.45/16.65  % done 6390 iterations in 16.190s
% 16.45/16.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 16.45/16.65  % SZS output start Refutation
% 16.45/16.65  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 16.45/16.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 16.45/16.65  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 16.45/16.65  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 16.45/16.65  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 16.45/16.65  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 16.45/16.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 16.45/16.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 16.45/16.65  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 16.45/16.65  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 16.45/16.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 16.45/16.65  thf(sk_A_type, type, sk_A: $i).
% 16.45/16.65  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 16.45/16.65  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 16.45/16.65  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 16.45/16.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 16.45/16.65  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 16.45/16.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 16.45/16.65  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 16.45/16.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 16.45/16.65  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 16.45/16.65  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 16.45/16.65  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 16.45/16.65  thf(sk_B_type, type, sk_B: $i).
% 16.45/16.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 16.45/16.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 16.45/16.65  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 16.45/16.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 16.45/16.65  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 16.45/16.65  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 16.45/16.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 16.45/16.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 16.45/16.65  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 16.45/16.65  thf(t87_funct_2, conjecture,
% 16.45/16.65    (![A:$i,B:$i]:
% 16.45/16.65     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 16.45/16.65         ( v3_funct_2 @ B @ A @ A ) & 
% 16.45/16.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 16.45/16.65       ( ![C:$i]:
% 16.45/16.65         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 16.45/16.65             ( v3_funct_2 @ C @ A @ A ) & 
% 16.45/16.65             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 16.45/16.65           ( ( r2_relset_1 @
% 16.45/16.65               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 16.45/16.65               ( k6_partfun1 @ A ) ) =>
% 16.45/16.65             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 16.45/16.65  thf(zf_stmt_0, negated_conjecture,
% 16.45/16.65    (~( ![A:$i,B:$i]:
% 16.45/16.65        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 16.45/16.65            ( v3_funct_2 @ B @ A @ A ) & 
% 16.45/16.65            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 16.45/16.65          ( ![C:$i]:
% 16.45/16.65            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 16.45/16.65                ( v3_funct_2 @ C @ A @ A ) & 
% 16.45/16.65                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 16.45/16.65              ( ( r2_relset_1 @
% 16.45/16.65                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 16.45/16.65                  ( k6_partfun1 @ A ) ) =>
% 16.45/16.65                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 16.45/16.65    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 16.45/16.65  thf('0', plain,
% 16.45/16.65      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('1', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf(redefinition_k2_funct_2, axiom,
% 16.45/16.65    (![A:$i,B:$i]:
% 16.45/16.65     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 16.45/16.65         ( v3_funct_2 @ B @ A @ A ) & 
% 16.45/16.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 16.45/16.65       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 16.45/16.65  thf('2', plain,
% 16.45/16.65      (![X85 : $i, X86 : $i]:
% 16.45/16.65         (((k2_funct_2 @ X86 @ X85) = (k2_funct_1 @ X85))
% 16.45/16.65          | ~ (m1_subset_1 @ X85 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X86 @ X86)))
% 16.45/16.65          | ~ (v3_funct_2 @ X85 @ X86 @ X86)
% 16.45/16.65          | ~ (v1_funct_2 @ X85 @ X86 @ X86)
% 16.45/16.65          | ~ (v1_funct_1 @ X85))),
% 16.45/16.65      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 16.45/16.65  thf('3', plain,
% 16.45/16.65      ((~ (v1_funct_1 @ sk_B)
% 16.45/16.65        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 16.45/16.65        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 16.45/16.65        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 16.45/16.65      inference('sup-', [status(thm)], ['1', '2'])).
% 16.45/16.65  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 16.45/16.65      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 16.45/16.65  thf('8', plain,
% 16.45/16.65      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_1 @ sk_B))),
% 16.45/16.65      inference('demod', [status(thm)], ['0', '7'])).
% 16.45/16.65  thf('9', plain,
% 16.45/16.65      ((r2_relset_1 @ sk_A @ sk_A @ 
% 16.45/16.65        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1) @ 
% 16.45/16.65        (k6_partfun1 @ sk_A))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf(redefinition_k6_partfun1, axiom,
% 16.45/16.65    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 16.45/16.65  thf('10', plain, (![X87 : $i]: ((k6_partfun1 @ X87) = (k6_relat_1 @ X87))),
% 16.45/16.65      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 16.45/16.65  thf('11', plain,
% 16.45/16.65      ((r2_relset_1 @ sk_A @ sk_A @ 
% 16.45/16.65        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1) @ 
% 16.45/16.65        (k6_relat_1 @ sk_A))),
% 16.45/16.65      inference('demod', [status(thm)], ['9', '10'])).
% 16.45/16.65  thf('12', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('13', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf(redefinition_k1_partfun1, axiom,
% 16.45/16.65    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 16.45/16.65     ( ( ( v1_funct_1 @ E ) & 
% 16.45/16.65         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 16.45/16.65         ( v1_funct_1 @ F ) & 
% 16.45/16.65         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 16.45/16.65       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 16.45/16.65  thf('14', plain,
% 16.45/16.65      (![X79 : $i, X80 : $i, X81 : $i, X82 : $i, X83 : $i, X84 : $i]:
% 16.45/16.65         (~ (m1_subset_1 @ X79 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X80 @ X81)))
% 16.45/16.65          | ~ (v1_funct_1 @ X79)
% 16.45/16.65          | ~ (v1_funct_1 @ X82)
% 16.45/16.65          | ~ (m1_subset_1 @ X82 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X83 @ X84)))
% 16.45/16.65          | ((k1_partfun1 @ X80 @ X81 @ X83 @ X84 @ X79 @ X82)
% 16.45/16.65              = (k5_relat_1 @ X79 @ X82)))),
% 16.45/16.65      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 16.45/16.65  thf('15', plain,
% 16.45/16.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.45/16.65         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 16.45/16.65            = (k5_relat_1 @ sk_B @ X0))
% 16.45/16.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 16.45/16.65          | ~ (v1_funct_1 @ X0)
% 16.45/16.65          | ~ (v1_funct_1 @ sk_B))),
% 16.45/16.65      inference('sup-', [status(thm)], ['13', '14'])).
% 16.45/16.65  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('17', plain,
% 16.45/16.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.45/16.65         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 16.45/16.65            = (k5_relat_1 @ sk_B @ X0))
% 16.45/16.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 16.45/16.65          | ~ (v1_funct_1 @ X0))),
% 16.45/16.65      inference('demod', [status(thm)], ['15', '16'])).
% 16.45/16.65  thf('18', plain,
% 16.45/16.65      ((~ (v1_funct_1 @ sk_C_1)
% 16.45/16.65        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1)
% 16.45/16.65            = (k5_relat_1 @ sk_B @ sk_C_1)))),
% 16.45/16.65      inference('sup-', [status(thm)], ['12', '17'])).
% 16.45/16.65  thf('19', plain, ((v1_funct_1 @ sk_C_1)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('20', plain,
% 16.45/16.65      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1)
% 16.45/16.65         = (k5_relat_1 @ sk_B @ sk_C_1))),
% 16.45/16.65      inference('demod', [status(thm)], ['18', '19'])).
% 16.45/16.65  thf('21', plain,
% 16.45/16.65      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_B @ sk_C_1) @ 
% 16.45/16.65        (k6_relat_1 @ sk_A))),
% 16.45/16.65      inference('demod', [status(thm)], ['11', '20'])).
% 16.45/16.65  thf('22', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('23', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf(dt_k1_partfun1, axiom,
% 16.45/16.65    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 16.45/16.65     ( ( ( v1_funct_1 @ E ) & 
% 16.45/16.65         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 16.45/16.65         ( v1_funct_1 @ F ) & 
% 16.45/16.65         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 16.45/16.65       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 16.45/16.65         ( m1_subset_1 @
% 16.45/16.65           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 16.45/16.65           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 16.45/16.65  thf('24', plain,
% 16.45/16.65      (![X69 : $i, X70 : $i, X71 : $i, X72 : $i, X73 : $i, X74 : $i]:
% 16.45/16.65         (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X70 @ X71)))
% 16.45/16.65          | ~ (v1_funct_1 @ X69)
% 16.45/16.65          | ~ (v1_funct_1 @ X72)
% 16.45/16.65          | ~ (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X73 @ X74)))
% 16.45/16.65          | (m1_subset_1 @ (k1_partfun1 @ X70 @ X71 @ X73 @ X74 @ X69 @ X72) @ 
% 16.45/16.65             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X70 @ X74))))),
% 16.45/16.65      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 16.45/16.65  thf('25', plain,
% 16.45/16.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.45/16.65         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 16.45/16.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 16.45/16.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 16.45/16.65          | ~ (v1_funct_1 @ X1)
% 16.45/16.65          | ~ (v1_funct_1 @ sk_B))),
% 16.45/16.65      inference('sup-', [status(thm)], ['23', '24'])).
% 16.45/16.65  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('27', plain,
% 16.45/16.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.45/16.65         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 16.45/16.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 16.45/16.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 16.45/16.65          | ~ (v1_funct_1 @ X1))),
% 16.45/16.65      inference('demod', [status(thm)], ['25', '26'])).
% 16.45/16.65  thf('28', plain,
% 16.45/16.65      ((~ (v1_funct_1 @ sk_C_1)
% 16.45/16.65        | (m1_subset_1 @ 
% 16.45/16.65           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1) @ 
% 16.45/16.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 16.45/16.65      inference('sup-', [status(thm)], ['22', '27'])).
% 16.45/16.65  thf('29', plain, ((v1_funct_1 @ sk_C_1)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('30', plain,
% 16.45/16.65      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1)
% 16.45/16.65         = (k5_relat_1 @ sk_B @ sk_C_1))),
% 16.45/16.65      inference('demod', [status(thm)], ['18', '19'])).
% 16.45/16.65  thf('31', plain,
% 16.45/16.65      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ sk_C_1) @ 
% 16.45/16.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('demod', [status(thm)], ['28', '29', '30'])).
% 16.45/16.65  thf(redefinition_r2_relset_1, axiom,
% 16.45/16.65    (![A:$i,B:$i,C:$i,D:$i]:
% 16.45/16.65     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 16.45/16.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 16.45/16.65       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 16.45/16.65  thf('32', plain,
% 16.45/16.65      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 16.45/16.65         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 16.45/16.65          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 16.45/16.65          | ((X45) = (X48))
% 16.45/16.65          | ~ (r2_relset_1 @ X46 @ X47 @ X45 @ X48))),
% 16.45/16.65      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 16.45/16.65  thf('33', plain,
% 16.45/16.65      (![X0 : $i]:
% 16.45/16.65         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_B @ sk_C_1) @ X0)
% 16.45/16.65          | ((k5_relat_1 @ sk_B @ sk_C_1) = (X0))
% 16.45/16.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 16.45/16.65      inference('sup-', [status(thm)], ['31', '32'])).
% 16.45/16.65  thf('34', plain,
% 16.45/16.65      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 16.45/16.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 16.45/16.65        | ((k5_relat_1 @ sk_B @ sk_C_1) = (k6_relat_1 @ sk_A)))),
% 16.45/16.65      inference('sup-', [status(thm)], ['21', '33'])).
% 16.45/16.65  thf(dt_k6_partfun1, axiom,
% 16.45/16.65    (![A:$i]:
% 16.45/16.65     ( ( m1_subset_1 @
% 16.45/16.65         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 16.45/16.65       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 16.45/16.65  thf('35', plain,
% 16.45/16.65      (![X78 : $i]:
% 16.45/16.65         (m1_subset_1 @ (k6_partfun1 @ X78) @ 
% 16.45/16.65          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X78 @ X78)))),
% 16.45/16.65      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 16.45/16.65  thf('36', plain, (![X87 : $i]: ((k6_partfun1 @ X87) = (k6_relat_1 @ X87))),
% 16.45/16.65      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 16.45/16.65  thf('37', plain,
% 16.45/16.65      (![X78 : $i]:
% 16.45/16.65         (m1_subset_1 @ (k6_relat_1 @ X78) @ 
% 16.45/16.65          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X78 @ X78)))),
% 16.45/16.65      inference('demod', [status(thm)], ['35', '36'])).
% 16.45/16.65  thf('38', plain, (((k5_relat_1 @ sk_B @ sk_C_1) = (k6_relat_1 @ sk_A))),
% 16.45/16.65      inference('demod', [status(thm)], ['34', '37'])).
% 16.45/16.65  thf('39', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf(t35_funct_2, axiom,
% 16.45/16.65    (![A:$i,B:$i,C:$i]:
% 16.45/16.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 16.45/16.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 16.45/16.65       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 16.45/16.65         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 16.45/16.65           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 16.45/16.65             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 16.45/16.65  thf('40', plain,
% 16.45/16.65      (![X88 : $i, X89 : $i, X90 : $i]:
% 16.45/16.65         (((X88) = (k1_xboole_0))
% 16.45/16.65          | ~ (v1_funct_1 @ X89)
% 16.45/16.65          | ~ (v1_funct_2 @ X89 @ X90 @ X88)
% 16.45/16.65          | ~ (m1_subset_1 @ X89 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X90 @ X88)))
% 16.45/16.65          | ((k5_relat_1 @ (k2_funct_1 @ X89) @ X89) = (k6_partfun1 @ X88))
% 16.45/16.65          | ~ (v2_funct_1 @ X89)
% 16.45/16.65          | ((k2_relset_1 @ X90 @ X88 @ X89) != (X88)))),
% 16.45/16.65      inference('cnf', [status(esa)], [t35_funct_2])).
% 16.45/16.65  thf('41', plain, (![X87 : $i]: ((k6_partfun1 @ X87) = (k6_relat_1 @ X87))),
% 16.45/16.65      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 16.45/16.65  thf('42', plain,
% 16.45/16.65      (![X88 : $i, X89 : $i, X90 : $i]:
% 16.45/16.65         (((X88) = (k1_xboole_0))
% 16.45/16.65          | ~ (v1_funct_1 @ X89)
% 16.45/16.65          | ~ (v1_funct_2 @ X89 @ X90 @ X88)
% 16.45/16.65          | ~ (m1_subset_1 @ X89 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X90 @ X88)))
% 16.45/16.65          | ((k5_relat_1 @ (k2_funct_1 @ X89) @ X89) = (k6_relat_1 @ X88))
% 16.45/16.65          | ~ (v2_funct_1 @ X89)
% 16.45/16.65          | ((k2_relset_1 @ X90 @ X88 @ X89) != (X88)))),
% 16.45/16.65      inference('demod', [status(thm)], ['40', '41'])).
% 16.45/16.65  thf('43', plain,
% 16.45/16.65      ((((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 16.45/16.65        | ~ (v2_funct_1 @ sk_B)
% 16.45/16.65        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_relat_1 @ sk_A))
% 16.45/16.65        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 16.45/16.65        | ~ (v1_funct_1 @ sk_B)
% 16.45/16.65        | ((sk_A) = (k1_xboole_0)))),
% 16.45/16.65      inference('sup-', [status(thm)], ['39', '42'])).
% 16.45/16.65  thf('44', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf(t38_relset_1, axiom,
% 16.45/16.65    (![A:$i,B:$i,C:$i]:
% 16.45/16.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.45/16.65       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 16.45/16.65         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 16.45/16.65  thf('45', plain,
% 16.45/16.65      (![X50 : $i, X51 : $i, X52 : $i]:
% 16.45/16.65         (((k7_relset_1 @ X50 @ X51 @ X52 @ X50)
% 16.45/16.65            = (k2_relset_1 @ X50 @ X51 @ X52))
% 16.45/16.65          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51))))),
% 16.45/16.65      inference('cnf', [status(esa)], [t38_relset_1])).
% 16.45/16.65  thf('46', plain,
% 16.45/16.65      (((k7_relset_1 @ sk_A @ sk_A @ sk_B @ sk_A)
% 16.45/16.65         = (k2_relset_1 @ sk_A @ sk_A @ sk_B))),
% 16.45/16.65      inference('sup-', [status(thm)], ['44', '45'])).
% 16.45/16.65  thf('47', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf(redefinition_k7_relset_1, axiom,
% 16.45/16.65    (![A:$i,B:$i,C:$i,D:$i]:
% 16.45/16.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.45/16.65       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 16.45/16.65  thf('48', plain,
% 16.45/16.65      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 16.45/16.65         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 16.45/16.65          | ((k7_relset_1 @ X42 @ X43 @ X41 @ X44) = (k9_relat_1 @ X41 @ X44)))),
% 16.45/16.65      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 16.45/16.65  thf('49', plain,
% 16.45/16.65      (![X0 : $i]:
% 16.45/16.65         ((k7_relset_1 @ sk_A @ sk_A @ sk_B @ X0) = (k9_relat_1 @ sk_B @ X0))),
% 16.45/16.65      inference('sup-', [status(thm)], ['47', '48'])).
% 16.45/16.65  thf('50', plain,
% 16.45/16.65      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relset_1 @ sk_A @ sk_A @ sk_B))),
% 16.45/16.65      inference('demod', [status(thm)], ['46', '49'])).
% 16.45/16.65  thf('51', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf(cc2_relset_1, axiom,
% 16.45/16.65    (![A:$i,B:$i,C:$i]:
% 16.45/16.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.45/16.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 16.45/16.65  thf('52', plain,
% 16.45/16.65      (![X35 : $i, X36 : $i, X37 : $i]:
% 16.45/16.65         ((v4_relat_1 @ X35 @ X36)
% 16.45/16.65          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 16.45/16.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 16.45/16.65  thf('53', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 16.45/16.65      inference('sup-', [status(thm)], ['51', '52'])).
% 16.45/16.65  thf(t209_relat_1, axiom,
% 16.45/16.65    (![A:$i,B:$i]:
% 16.45/16.65     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 16.45/16.65       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 16.45/16.65  thf('54', plain,
% 16.45/16.65      (![X22 : $i, X23 : $i]:
% 16.45/16.65         (((X22) = (k7_relat_1 @ X22 @ X23))
% 16.45/16.65          | ~ (v4_relat_1 @ X22 @ X23)
% 16.45/16.65          | ~ (v1_relat_1 @ X22))),
% 16.45/16.65      inference('cnf', [status(esa)], [t209_relat_1])).
% 16.45/16.65  thf('55', plain,
% 16.45/16.65      ((~ (v1_relat_1 @ sk_B) | ((sk_B) = (k7_relat_1 @ sk_B @ sk_A)))),
% 16.45/16.65      inference('sup-', [status(thm)], ['53', '54'])).
% 16.45/16.65  thf('56', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf(cc2_relat_1, axiom,
% 16.45/16.65    (![A:$i]:
% 16.45/16.65     ( ( v1_relat_1 @ A ) =>
% 16.45/16.65       ( ![B:$i]:
% 16.45/16.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 16.45/16.65  thf('57', plain,
% 16.45/16.65      (![X15 : $i, X16 : $i]:
% 16.45/16.65         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 16.45/16.65          | (v1_relat_1 @ X15)
% 16.45/16.65          | ~ (v1_relat_1 @ X16))),
% 16.45/16.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 16.45/16.65  thf('58', plain,
% 16.45/16.65      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 16.45/16.65      inference('sup-', [status(thm)], ['56', '57'])).
% 16.45/16.65  thf(fc6_relat_1, axiom,
% 16.45/16.65    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 16.45/16.65  thf('59', plain,
% 16.45/16.65      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 16.45/16.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 16.45/16.65  thf('60', plain, ((v1_relat_1 @ sk_B)),
% 16.45/16.65      inference('demod', [status(thm)], ['58', '59'])).
% 16.45/16.65  thf('61', plain, (((sk_B) = (k7_relat_1 @ sk_B @ sk_A))),
% 16.45/16.65      inference('demod', [status(thm)], ['55', '60'])).
% 16.45/16.65  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 16.45/16.65      inference('demod', [status(thm)], ['58', '59'])).
% 16.45/16.65  thf(t148_relat_1, axiom,
% 16.45/16.65    (![A:$i,B:$i]:
% 16.45/16.65     ( ( v1_relat_1 @ B ) =>
% 16.45/16.65       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 16.45/16.65  thf('63', plain,
% 16.45/16.65      (![X20 : $i, X21 : $i]:
% 16.45/16.65         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 16.45/16.65          | ~ (v1_relat_1 @ X20))),
% 16.45/16.65      inference('cnf', [status(esa)], [t148_relat_1])).
% 16.45/16.65  thf('64', plain,
% 16.45/16.65      (![X0 : $i]:
% 16.45/16.65         ((k2_relat_1 @ (k7_relat_1 @ sk_B @ X0)) = (k9_relat_1 @ sk_B @ X0))),
% 16.45/16.65      inference('sup-', [status(thm)], ['62', '63'])).
% 16.45/16.65  thf('65', plain, (((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ sk_A))),
% 16.45/16.65      inference('sup+', [status(thm)], ['61', '64'])).
% 16.45/16.65  thf('66', plain,
% 16.45/16.65      (((k2_relat_1 @ sk_B) = (k2_relset_1 @ sk_A @ sk_A @ sk_B))),
% 16.45/16.65      inference('demod', [status(thm)], ['50', '65'])).
% 16.45/16.65  thf('67', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf(cc2_funct_2, axiom,
% 16.45/16.65    (![A:$i,B:$i,C:$i]:
% 16.45/16.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.45/16.65       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 16.45/16.65         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 16.45/16.65  thf('68', plain,
% 16.45/16.65      (![X56 : $i, X57 : $i, X58 : $i]:
% 16.45/16.65         (~ (v1_funct_1 @ X56)
% 16.45/16.65          | ~ (v3_funct_2 @ X56 @ X57 @ X58)
% 16.45/16.65          | (v2_funct_2 @ X56 @ X58)
% 16.45/16.65          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58))))),
% 16.45/16.65      inference('cnf', [status(esa)], [cc2_funct_2])).
% 16.45/16.65  thf('69', plain,
% 16.45/16.65      (((v2_funct_2 @ sk_B @ sk_A)
% 16.45/16.65        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 16.45/16.65        | ~ (v1_funct_1 @ sk_B))),
% 16.45/16.65      inference('sup-', [status(thm)], ['67', '68'])).
% 16.45/16.65  thf('70', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('71', plain, ((v1_funct_1 @ sk_B)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('72', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 16.45/16.65      inference('demod', [status(thm)], ['69', '70', '71'])).
% 16.45/16.65  thf(d3_funct_2, axiom,
% 16.45/16.65    (![A:$i,B:$i]:
% 16.45/16.65     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 16.45/16.65       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 16.45/16.65  thf('73', plain,
% 16.45/16.65      (![X67 : $i, X68 : $i]:
% 16.45/16.65         (~ (v2_funct_2 @ X68 @ X67)
% 16.45/16.65          | ((k2_relat_1 @ X68) = (X67))
% 16.45/16.65          | ~ (v5_relat_1 @ X68 @ X67)
% 16.45/16.65          | ~ (v1_relat_1 @ X68))),
% 16.45/16.65      inference('cnf', [status(esa)], [d3_funct_2])).
% 16.45/16.65  thf('74', plain,
% 16.45/16.65      ((~ (v1_relat_1 @ sk_B)
% 16.45/16.65        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 16.45/16.65        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 16.45/16.65      inference('sup-', [status(thm)], ['72', '73'])).
% 16.45/16.65  thf('75', plain, ((v1_relat_1 @ sk_B)),
% 16.45/16.65      inference('demod', [status(thm)], ['58', '59'])).
% 16.45/16.65  thf('76', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('77', plain,
% 16.45/16.65      (![X35 : $i, X36 : $i, X37 : $i]:
% 16.45/16.65         ((v5_relat_1 @ X35 @ X37)
% 16.45/16.65          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 16.45/16.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 16.45/16.65  thf('78', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 16.45/16.65      inference('sup-', [status(thm)], ['76', '77'])).
% 16.45/16.65  thf('79', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 16.45/16.65      inference('demod', [status(thm)], ['74', '75', '78'])).
% 16.45/16.65  thf('80', plain, (((sk_A) = (k2_relset_1 @ sk_A @ sk_A @ sk_B))),
% 16.45/16.65      inference('demod', [status(thm)], ['66', '79'])).
% 16.45/16.65  thf('81', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('82', plain,
% 16.45/16.65      (![X56 : $i, X57 : $i, X58 : $i]:
% 16.45/16.65         (~ (v1_funct_1 @ X56)
% 16.45/16.65          | ~ (v3_funct_2 @ X56 @ X57 @ X58)
% 16.45/16.65          | (v2_funct_1 @ X56)
% 16.45/16.65          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58))))),
% 16.45/16.65      inference('cnf', [status(esa)], [cc2_funct_2])).
% 16.45/16.65  thf('83', plain,
% 16.45/16.65      (((v2_funct_1 @ sk_B)
% 16.45/16.65        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 16.45/16.65        | ~ (v1_funct_1 @ sk_B))),
% 16.45/16.65      inference('sup-', [status(thm)], ['81', '82'])).
% 16.45/16.65  thf('84', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('85', plain, ((v1_funct_1 @ sk_B)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('86', plain, ((v2_funct_1 @ sk_B)),
% 16.45/16.65      inference('demod', [status(thm)], ['83', '84', '85'])).
% 16.45/16.65  thf('87', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('88', plain, ((v1_funct_1 @ sk_B)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('89', plain,
% 16.45/16.65      ((((sk_A) != (sk_A))
% 16.45/16.65        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_relat_1 @ sk_A))
% 16.45/16.65        | ((sk_A) = (k1_xboole_0)))),
% 16.45/16.65      inference('demod', [status(thm)], ['43', '80', '86', '87', '88'])).
% 16.45/16.65  thf('90', plain,
% 16.45/16.65      ((((sk_A) = (k1_xboole_0))
% 16.45/16.65        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_relat_1 @ sk_A)))),
% 16.45/16.65      inference('simplify', [status(thm)], ['89'])).
% 16.45/16.65  thf(t55_relat_1, axiom,
% 16.45/16.65    (![A:$i]:
% 16.45/16.65     ( ( v1_relat_1 @ A ) =>
% 16.45/16.65       ( ![B:$i]:
% 16.45/16.65         ( ( v1_relat_1 @ B ) =>
% 16.45/16.65           ( ![C:$i]:
% 16.45/16.65             ( ( v1_relat_1 @ C ) =>
% 16.45/16.65               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 16.45/16.65                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 16.45/16.65  thf('91', plain,
% 16.45/16.65      (![X24 : $i, X25 : $i, X26 : $i]:
% 16.45/16.65         (~ (v1_relat_1 @ X24)
% 16.45/16.65          | ((k5_relat_1 @ (k5_relat_1 @ X25 @ X24) @ X26)
% 16.45/16.65              = (k5_relat_1 @ X25 @ (k5_relat_1 @ X24 @ X26)))
% 16.45/16.65          | ~ (v1_relat_1 @ X26)
% 16.45/16.65          | ~ (v1_relat_1 @ X25))),
% 16.45/16.65      inference('cnf', [status(esa)], [t55_relat_1])).
% 16.45/16.65  thf('92', plain,
% 16.45/16.65      (![X0 : $i]:
% 16.45/16.65         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 16.45/16.65            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k5_relat_1 @ sk_B @ X0)))
% 16.45/16.65          | ((sk_A) = (k1_xboole_0))
% 16.45/16.65          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 16.45/16.65          | ~ (v1_relat_1 @ X0)
% 16.45/16.65          | ~ (v1_relat_1 @ sk_B))),
% 16.45/16.65      inference('sup+', [status(thm)], ['90', '91'])).
% 16.45/16.65  thf('93', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf(dt_k2_funct_2, axiom,
% 16.45/16.65    (![A:$i,B:$i]:
% 16.45/16.65     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 16.45/16.65         ( v3_funct_2 @ B @ A @ A ) & 
% 16.45/16.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 16.45/16.65       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 16.45/16.65         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 16.45/16.65         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 16.45/16.65         ( m1_subset_1 @
% 16.45/16.65           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 16.45/16.65  thf('94', plain,
% 16.45/16.65      (![X75 : $i, X76 : $i]:
% 16.45/16.65         ((m1_subset_1 @ (k2_funct_2 @ X75 @ X76) @ 
% 16.45/16.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X75 @ X75)))
% 16.45/16.65          | ~ (m1_subset_1 @ X76 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X75 @ X75)))
% 16.45/16.65          | ~ (v3_funct_2 @ X76 @ X75 @ X75)
% 16.45/16.65          | ~ (v1_funct_2 @ X76 @ X75 @ X75)
% 16.45/16.65          | ~ (v1_funct_1 @ X76))),
% 16.45/16.65      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 16.45/16.65  thf('95', plain,
% 16.45/16.65      ((~ (v1_funct_1 @ sk_B)
% 16.45/16.65        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 16.45/16.65        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 16.45/16.65        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 16.45/16.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 16.45/16.65      inference('sup-', [status(thm)], ['93', '94'])).
% 16.45/16.65  thf('96', plain, ((v1_funct_1 @ sk_B)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('97', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('98', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('99', plain,
% 16.45/16.65      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 16.45/16.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 16.45/16.65  thf(cc1_relset_1, axiom,
% 16.45/16.65    (![A:$i,B:$i,C:$i]:
% 16.45/16.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.45/16.65       ( v1_relat_1 @ C ) ))).
% 16.45/16.65  thf('100', plain,
% 16.45/16.65      (![X32 : $i, X33 : $i, X34 : $i]:
% 16.45/16.65         ((v1_relat_1 @ X32)
% 16.45/16.65          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 16.45/16.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 16.45/16.65  thf('101', plain, ((v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 16.45/16.65      inference('sup-', [status(thm)], ['99', '100'])).
% 16.45/16.65  thf('102', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 16.45/16.65      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 16.45/16.65  thf('103', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 16.45/16.65      inference('demod', [status(thm)], ['101', '102'])).
% 16.45/16.65  thf('104', plain, ((v1_relat_1 @ sk_B)),
% 16.45/16.65      inference('demod', [status(thm)], ['58', '59'])).
% 16.45/16.65  thf('105', plain,
% 16.45/16.65      (![X0 : $i]:
% 16.45/16.65         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 16.45/16.65            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k5_relat_1 @ sk_B @ X0)))
% 16.45/16.65          | ((sk_A) = (k1_xboole_0))
% 16.45/16.65          | ~ (v1_relat_1 @ X0))),
% 16.45/16.65      inference('demod', [status(thm)], ['92', '103', '104'])).
% 16.45/16.65  thf('106', plain,
% 16.45/16.65      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C_1)
% 16.45/16.65          = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k6_relat_1 @ sk_A)))
% 16.45/16.65        | ~ (v1_relat_1 @ sk_C_1)
% 16.45/16.65        | ((sk_A) = (k1_xboole_0)))),
% 16.45/16.65      inference('sup+', [status(thm)], ['38', '105'])).
% 16.45/16.65  thf('107', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf(d1_funct_2, axiom,
% 16.45/16.65    (![A:$i,B:$i,C:$i]:
% 16.45/16.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.45/16.65       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 16.45/16.65           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 16.45/16.65             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 16.45/16.65         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 16.45/16.65           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 16.45/16.65             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 16.45/16.65  thf(zf_stmt_1, axiom,
% 16.45/16.65    (![C:$i,B:$i,A:$i]:
% 16.45/16.65     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 16.45/16.65       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 16.45/16.65  thf('108', plain,
% 16.45/16.65      (![X61 : $i, X62 : $i, X63 : $i]:
% 16.45/16.65         (~ (v1_funct_2 @ X63 @ X61 @ X62)
% 16.45/16.65          | ((X61) = (k1_relset_1 @ X61 @ X62 @ X63))
% 16.45/16.65          | ~ (zip_tseitin_1 @ X63 @ X62 @ X61))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 16.45/16.65  thf('109', plain,
% 16.45/16.65      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)
% 16.45/16.65        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_C_1)))),
% 16.45/16.65      inference('sup-', [status(thm)], ['107', '108'])).
% 16.45/16.65  thf('110', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf(redefinition_k1_relset_1, axiom,
% 16.45/16.65    (![A:$i,B:$i,C:$i]:
% 16.45/16.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.45/16.65       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 16.45/16.65  thf('111', plain,
% 16.45/16.65      (![X38 : $i, X39 : $i, X40 : $i]:
% 16.45/16.65         (((k1_relset_1 @ X39 @ X40 @ X38) = (k1_relat_1 @ X38))
% 16.45/16.65          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 16.45/16.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 16.45/16.65  thf('112', plain,
% 16.45/16.65      (((k1_relset_1 @ sk_A @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 16.45/16.65      inference('sup-', [status(thm)], ['110', '111'])).
% 16.45/16.65  thf('113', plain,
% 16.45/16.65      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)
% 16.45/16.65        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 16.45/16.65      inference('demod', [status(thm)], ['109', '112'])).
% 16.45/16.65  thf('114', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 16.45/16.65  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 16.45/16.65  thf(zf_stmt_4, axiom,
% 16.45/16.65    (![B:$i,A:$i]:
% 16.45/16.65     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 16.45/16.65       ( zip_tseitin_0 @ B @ A ) ))).
% 16.45/16.65  thf(zf_stmt_5, axiom,
% 16.45/16.65    (![A:$i,B:$i,C:$i]:
% 16.45/16.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.45/16.65       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 16.45/16.65         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 16.45/16.65           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 16.45/16.65             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 16.45/16.65  thf('115', plain,
% 16.45/16.65      (![X64 : $i, X65 : $i, X66 : $i]:
% 16.45/16.65         (~ (zip_tseitin_0 @ X64 @ X65)
% 16.45/16.65          | (zip_tseitin_1 @ X66 @ X64 @ X65)
% 16.45/16.65          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X64))))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 16.45/16.65  thf('116', plain,
% 16.45/16.65      (((zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)
% 16.45/16.65        | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 16.45/16.65      inference('sup-', [status(thm)], ['114', '115'])).
% 16.45/16.65  thf('117', plain,
% 16.45/16.65      (![X59 : $i, X60 : $i]:
% 16.45/16.65         ((zip_tseitin_0 @ X59 @ X60) | ((X59) = (k1_xboole_0)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_4])).
% 16.45/16.65  thf('118', plain,
% 16.45/16.65      (![X59 : $i, X60 : $i]:
% 16.45/16.65         ((zip_tseitin_0 @ X59 @ X60) | ((X60) != (k1_xboole_0)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_4])).
% 16.45/16.65  thf('119', plain, (![X59 : $i]: (zip_tseitin_0 @ X59 @ k1_xboole_0)),
% 16.45/16.65      inference('simplify', [status(thm)], ['118'])).
% 16.45/16.65  thf('120', plain,
% 16.45/16.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.45/16.65         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 16.45/16.65      inference('sup+', [status(thm)], ['117', '119'])).
% 16.45/16.65  thf('121', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 16.45/16.65      inference('eq_fact', [status(thm)], ['120'])).
% 16.45/16.65  thf('122', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)),
% 16.45/16.65      inference('demod', [status(thm)], ['116', '121'])).
% 16.45/16.65  thf('123', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 16.45/16.65      inference('demod', [status(thm)], ['113', '122'])).
% 16.45/16.65  thf(t78_relat_1, axiom,
% 16.45/16.65    (![A:$i]:
% 16.45/16.65     ( ( v1_relat_1 @ A ) =>
% 16.45/16.65       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 16.45/16.65  thf('124', plain,
% 16.45/16.65      (![X28 : $i]:
% 16.45/16.65         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X28)) @ X28) = (X28))
% 16.45/16.65          | ~ (v1_relat_1 @ X28))),
% 16.45/16.65      inference('cnf', [status(esa)], [t78_relat_1])).
% 16.45/16.65  thf('125', plain,
% 16.45/16.65      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C_1) = (sk_C_1))
% 16.45/16.65        | ~ (v1_relat_1 @ sk_C_1))),
% 16.45/16.65      inference('sup+', [status(thm)], ['123', '124'])).
% 16.45/16.65  thf('126', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('127', plain,
% 16.45/16.65      (![X15 : $i, X16 : $i]:
% 16.45/16.65         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 16.45/16.65          | (v1_relat_1 @ X15)
% 16.45/16.65          | ~ (v1_relat_1 @ X16))),
% 16.45/16.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 16.45/16.65  thf('128', plain,
% 16.45/16.65      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C_1))),
% 16.45/16.65      inference('sup-', [status(thm)], ['126', '127'])).
% 16.45/16.65  thf('129', plain,
% 16.45/16.65      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 16.45/16.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 16.45/16.65  thf('130', plain, ((v1_relat_1 @ sk_C_1)),
% 16.45/16.65      inference('demod', [status(thm)], ['128', '129'])).
% 16.45/16.65  thf('131', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C_1) = (sk_C_1))),
% 16.45/16.65      inference('demod', [status(thm)], ['125', '130'])).
% 16.45/16.65  thf('132', plain,
% 16.45/16.65      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 16.45/16.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 16.45/16.65  thf('133', plain,
% 16.45/16.65      (![X56 : $i, X57 : $i, X58 : $i]:
% 16.45/16.65         (~ (v1_funct_1 @ X56)
% 16.45/16.65          | ~ (v3_funct_2 @ X56 @ X57 @ X58)
% 16.45/16.65          | (v2_funct_2 @ X56 @ X58)
% 16.45/16.65          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58))))),
% 16.45/16.65      inference('cnf', [status(esa)], [cc2_funct_2])).
% 16.45/16.65  thf('134', plain,
% 16.45/16.65      (((v2_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A)
% 16.45/16.65        | ~ (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A)
% 16.45/16.65        | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 16.45/16.65      inference('sup-', [status(thm)], ['132', '133'])).
% 16.45/16.65  thf('135', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('136', plain,
% 16.45/16.65      (![X75 : $i, X76 : $i]:
% 16.45/16.65         ((v3_funct_2 @ (k2_funct_2 @ X75 @ X76) @ X75 @ X75)
% 16.45/16.65          | ~ (m1_subset_1 @ X76 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X75 @ X75)))
% 16.45/16.65          | ~ (v3_funct_2 @ X76 @ X75 @ X75)
% 16.45/16.65          | ~ (v1_funct_2 @ X76 @ X75 @ X75)
% 16.45/16.65          | ~ (v1_funct_1 @ X76))),
% 16.45/16.65      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 16.45/16.65  thf('137', plain,
% 16.45/16.65      ((~ (v1_funct_1 @ sk_B)
% 16.45/16.65        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 16.45/16.65        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 16.45/16.65        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 16.45/16.65      inference('sup-', [status(thm)], ['135', '136'])).
% 16.45/16.65  thf('138', plain, ((v1_funct_1 @ sk_B)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('139', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('140', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('141', plain, ((v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A)),
% 16.45/16.65      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 16.45/16.65  thf('142', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('143', plain,
% 16.45/16.65      (![X75 : $i, X76 : $i]:
% 16.45/16.65         ((v1_funct_1 @ (k2_funct_2 @ X75 @ X76))
% 16.45/16.65          | ~ (m1_subset_1 @ X76 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X75 @ X75)))
% 16.45/16.65          | ~ (v3_funct_2 @ X76 @ X75 @ X75)
% 16.45/16.65          | ~ (v1_funct_2 @ X76 @ X75 @ X75)
% 16.45/16.65          | ~ (v1_funct_1 @ X76))),
% 16.45/16.65      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 16.45/16.65  thf('144', plain,
% 16.45/16.65      ((~ (v1_funct_1 @ sk_B)
% 16.45/16.65        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 16.45/16.65        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 16.45/16.65        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 16.45/16.65      inference('sup-', [status(thm)], ['142', '143'])).
% 16.45/16.65  thf('145', plain, ((v1_funct_1 @ sk_B)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('146', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('147', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('148', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 16.45/16.65      inference('demod', [status(thm)], ['144', '145', '146', '147'])).
% 16.45/16.65  thf('149', plain, ((v2_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A)),
% 16.45/16.65      inference('demod', [status(thm)], ['134', '141', '148'])).
% 16.45/16.65  thf('150', plain,
% 16.45/16.65      (![X67 : $i, X68 : $i]:
% 16.45/16.65         (~ (v2_funct_2 @ X68 @ X67)
% 16.45/16.65          | ((k2_relat_1 @ X68) = (X67))
% 16.45/16.65          | ~ (v5_relat_1 @ X68 @ X67)
% 16.45/16.65          | ~ (v1_relat_1 @ X68))),
% 16.45/16.65      inference('cnf', [status(esa)], [d3_funct_2])).
% 16.45/16.65  thf('151', plain,
% 16.45/16.65      ((~ (v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_B))
% 16.45/16.65        | ~ (v5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A)
% 16.45/16.65        | ((k2_relat_1 @ (k2_funct_2 @ sk_A @ sk_B)) = (sk_A)))),
% 16.45/16.65      inference('sup-', [status(thm)], ['149', '150'])).
% 16.45/16.65  thf('152', plain, ((v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 16.45/16.65      inference('sup-', [status(thm)], ['99', '100'])).
% 16.45/16.65  thf('153', plain,
% 16.45/16.65      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 16.45/16.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 16.45/16.65  thf('154', plain,
% 16.45/16.65      (![X35 : $i, X36 : $i, X37 : $i]:
% 16.45/16.65         ((v5_relat_1 @ X35 @ X37)
% 16.45/16.65          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 16.45/16.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 16.45/16.65  thf('155', plain, ((v5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A)),
% 16.45/16.65      inference('sup-', [status(thm)], ['153', '154'])).
% 16.45/16.65  thf('156', plain, (((k2_relat_1 @ (k2_funct_2 @ sk_A @ sk_B)) = (sk_A))),
% 16.45/16.65      inference('demod', [status(thm)], ['151', '152', '155'])).
% 16.45/16.65  thf('157', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 16.45/16.65      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 16.45/16.65  thf('158', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 16.45/16.65      inference('demod', [status(thm)], ['156', '157'])).
% 16.45/16.65  thf(t80_relat_1, axiom,
% 16.45/16.65    (![A:$i]:
% 16.45/16.65     ( ( v1_relat_1 @ A ) =>
% 16.45/16.65       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 16.45/16.65  thf('159', plain,
% 16.45/16.65      (![X29 : $i]:
% 16.45/16.65         (((k5_relat_1 @ X29 @ (k6_relat_1 @ (k2_relat_1 @ X29))) = (X29))
% 16.45/16.65          | ~ (v1_relat_1 @ X29))),
% 16.45/16.65      inference('cnf', [status(esa)], [t80_relat_1])).
% 16.45/16.65  thf('160', plain,
% 16.45/16.65      ((((k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 16.45/16.65          = (k2_funct_1 @ sk_B))
% 16.45/16.65        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 16.45/16.65      inference('sup+', [status(thm)], ['158', '159'])).
% 16.45/16.65  thf('161', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 16.45/16.65      inference('demod', [status(thm)], ['101', '102'])).
% 16.45/16.65  thf('162', plain,
% 16.45/16.65      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 16.45/16.65         = (k2_funct_1 @ sk_B))),
% 16.45/16.65      inference('demod', [status(thm)], ['160', '161'])).
% 16.45/16.65  thf('163', plain, ((v1_relat_1 @ sk_C_1)),
% 16.45/16.65      inference('demod', [status(thm)], ['128', '129'])).
% 16.45/16.65  thf('164', plain,
% 16.45/16.65      ((((sk_C_1) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 16.45/16.65      inference('demod', [status(thm)], ['106', '131', '162', '163'])).
% 16.45/16.65  thf('165', plain,
% 16.45/16.65      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_1 @ sk_B))),
% 16.45/16.65      inference('demod', [status(thm)], ['0', '7'])).
% 16.45/16.65  thf('166', plain,
% 16.45/16.65      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1)
% 16.45/16.65        | ((sk_A) = (k1_xboole_0)))),
% 16.45/16.65      inference('sup-', [status(thm)], ['164', '165'])).
% 16.45/16.65  thf('167', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('168', plain,
% 16.45/16.65      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 16.45/16.65         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 16.45/16.65          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 16.45/16.65          | (r2_relset_1 @ X46 @ X47 @ X45 @ X48)
% 16.45/16.65          | ((X45) != (X48)))),
% 16.45/16.65      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 16.45/16.65  thf('169', plain,
% 16.45/16.65      (![X46 : $i, X47 : $i, X48 : $i]:
% 16.45/16.65         ((r2_relset_1 @ X46 @ X47 @ X48 @ X48)
% 16.45/16.65          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 16.45/16.65      inference('simplify', [status(thm)], ['168'])).
% 16.45/16.65  thf('170', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1)),
% 16.45/16.65      inference('sup-', [status(thm)], ['167', '169'])).
% 16.45/16.65  thf('171', plain, (((sk_A) = (k1_xboole_0))),
% 16.45/16.65      inference('demod', [status(thm)], ['166', '170'])).
% 16.45/16.65  thf('172', plain, (((sk_A) = (k1_xboole_0))),
% 16.45/16.65      inference('demod', [status(thm)], ['166', '170'])).
% 16.45/16.65  thf('173', plain,
% 16.45/16.65      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 @ 
% 16.45/16.65          (k2_funct_1 @ sk_B))),
% 16.45/16.65      inference('demod', [status(thm)], ['8', '171', '172'])).
% 16.45/16.65  thf('174', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 16.45/16.65      inference('demod', [status(thm)], ['113', '122'])).
% 16.45/16.65  thf(t64_relat_1, axiom,
% 16.45/16.65    (![A:$i]:
% 16.45/16.65     ( ( v1_relat_1 @ A ) =>
% 16.45/16.65       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 16.45/16.65           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 16.45/16.65         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 16.45/16.65  thf('175', plain,
% 16.45/16.65      (![X27 : $i]:
% 16.45/16.65         (((k1_relat_1 @ X27) != (k1_xboole_0))
% 16.45/16.65          | ((X27) = (k1_xboole_0))
% 16.45/16.65          | ~ (v1_relat_1 @ X27))),
% 16.45/16.65      inference('cnf', [status(esa)], [t64_relat_1])).
% 16.45/16.65  thf('176', plain,
% 16.45/16.65      ((((sk_A) != (k1_xboole_0))
% 16.45/16.65        | ~ (v1_relat_1 @ sk_C_1)
% 16.45/16.65        | ((sk_C_1) = (k1_xboole_0)))),
% 16.45/16.65      inference('sup-', [status(thm)], ['174', '175'])).
% 16.45/16.65  thf('177', plain, ((v1_relat_1 @ sk_C_1)),
% 16.45/16.65      inference('demod', [status(thm)], ['128', '129'])).
% 16.45/16.65  thf('178', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 16.45/16.65      inference('demod', [status(thm)], ['176', '177'])).
% 16.45/16.65  thf('179', plain, (((sk_A) = (k1_xboole_0))),
% 16.45/16.65      inference('demod', [status(thm)], ['166', '170'])).
% 16.45/16.65  thf('180', plain,
% 16.45/16.65      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 16.45/16.65      inference('demod', [status(thm)], ['178', '179'])).
% 16.45/16.65  thf('181', plain, (((sk_C_1) = (k1_xboole_0))),
% 16.45/16.65      inference('simplify', [status(thm)], ['180'])).
% 16.45/16.65  thf('182', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('183', plain,
% 16.45/16.65      (![X61 : $i, X62 : $i, X63 : $i]:
% 16.45/16.65         (~ (v1_funct_2 @ X63 @ X61 @ X62)
% 16.45/16.65          | ((X61) = (k1_relset_1 @ X61 @ X62 @ X63))
% 16.45/16.65          | ~ (zip_tseitin_1 @ X63 @ X62 @ X61))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 16.45/16.65  thf('184', plain,
% 16.45/16.65      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 16.45/16.65        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 16.45/16.65      inference('sup-', [status(thm)], ['182', '183'])).
% 16.45/16.65  thf('185', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('186', plain,
% 16.45/16.65      (![X38 : $i, X39 : $i, X40 : $i]:
% 16.45/16.65         (((k1_relset_1 @ X39 @ X40 @ X38) = (k1_relat_1 @ X38))
% 16.45/16.65          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 16.45/16.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 16.45/16.65  thf('187', plain,
% 16.45/16.65      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 16.45/16.65      inference('sup-', [status(thm)], ['185', '186'])).
% 16.45/16.65  thf('188', plain,
% 16.45/16.65      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_B)))),
% 16.45/16.65      inference('demod', [status(thm)], ['184', '187'])).
% 16.45/16.65  thf('189', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('190', plain,
% 16.45/16.65      (![X64 : $i, X65 : $i, X66 : $i]:
% 16.45/16.65         (~ (zip_tseitin_0 @ X64 @ X65)
% 16.45/16.65          | (zip_tseitin_1 @ X66 @ X64 @ X65)
% 16.45/16.65          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X64))))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 16.45/16.65  thf('191', plain,
% 16.45/16.65      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 16.45/16.65      inference('sup-', [status(thm)], ['189', '190'])).
% 16.45/16.65  thf('192', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 16.45/16.65      inference('eq_fact', [status(thm)], ['120'])).
% 16.45/16.65  thf('193', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 16.45/16.65      inference('demod', [status(thm)], ['191', '192'])).
% 16.45/16.65  thf('194', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 16.45/16.65      inference('demod', [status(thm)], ['188', '193'])).
% 16.45/16.65  thf('195', plain,
% 16.45/16.65      (![X27 : $i]:
% 16.45/16.65         (((k1_relat_1 @ X27) != (k1_xboole_0))
% 16.45/16.65          | ((X27) = (k1_xboole_0))
% 16.45/16.65          | ~ (v1_relat_1 @ X27))),
% 16.45/16.65      inference('cnf', [status(esa)], [t64_relat_1])).
% 16.45/16.65  thf('196', plain,
% 16.45/16.65      ((((sk_A) != (k1_xboole_0))
% 16.45/16.65        | ~ (v1_relat_1 @ sk_B)
% 16.45/16.65        | ((sk_B) = (k1_xboole_0)))),
% 16.45/16.65      inference('sup-', [status(thm)], ['194', '195'])).
% 16.45/16.65  thf('197', plain, ((v1_relat_1 @ sk_B)),
% 16.45/16.65      inference('demod', [status(thm)], ['58', '59'])).
% 16.45/16.65  thf('198', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 16.45/16.65      inference('demod', [status(thm)], ['196', '197'])).
% 16.45/16.65  thf('199', plain, (((sk_A) = (k1_xboole_0))),
% 16.45/16.65      inference('demod', [status(thm)], ['166', '170'])).
% 16.45/16.65  thf('200', plain,
% 16.45/16.65      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 16.45/16.65      inference('demod', [status(thm)], ['198', '199'])).
% 16.45/16.65  thf('201', plain, (((sk_B) = (k1_xboole_0))),
% 16.45/16.65      inference('simplify', [status(thm)], ['200'])).
% 16.45/16.65  thf('202', plain, (((k2_relat_1 @ (k2_funct_2 @ sk_A @ sk_B)) = (sk_A))),
% 16.45/16.65      inference('demod', [status(thm)], ['151', '152', '155'])).
% 16.45/16.65  thf('203', plain,
% 16.45/16.65      (![X27 : $i]:
% 16.45/16.65         (((k2_relat_1 @ X27) != (k1_xboole_0))
% 16.45/16.65          | ((X27) = (k1_xboole_0))
% 16.45/16.65          | ~ (v1_relat_1 @ X27))),
% 16.45/16.65      inference('cnf', [status(esa)], [t64_relat_1])).
% 16.45/16.65  thf('204', plain,
% 16.45/16.65      ((((sk_A) != (k1_xboole_0))
% 16.45/16.65        | ~ (v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_B))
% 16.45/16.65        | ((k2_funct_2 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 16.45/16.65      inference('sup-', [status(thm)], ['202', '203'])).
% 16.45/16.65  thf('205', plain, ((v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 16.45/16.65      inference('sup-', [status(thm)], ['99', '100'])).
% 16.45/16.65  thf('206', plain,
% 16.45/16.65      ((((sk_A) != (k1_xboole_0))
% 16.45/16.65        | ((k2_funct_2 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 16.45/16.65      inference('demod', [status(thm)], ['204', '205'])).
% 16.45/16.65  thf('207', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 16.45/16.65      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 16.45/16.65  thf('208', plain,
% 16.45/16.65      ((((sk_A) != (k1_xboole_0)) | ((k2_funct_1 @ sk_B) = (k1_xboole_0)))),
% 16.45/16.65      inference('demod', [status(thm)], ['206', '207'])).
% 16.45/16.65  thf('209', plain, (((sk_A) = (k1_xboole_0))),
% 16.45/16.65      inference('demod', [status(thm)], ['166', '170'])).
% 16.45/16.65  thf('210', plain,
% 16.45/16.65      ((((k1_xboole_0) != (k1_xboole_0))
% 16.45/16.65        | ((k2_funct_1 @ sk_B) = (k1_xboole_0)))),
% 16.45/16.65      inference('demod', [status(thm)], ['208', '209'])).
% 16.45/16.65  thf('211', plain, (((k2_funct_1 @ sk_B) = (k1_xboole_0))),
% 16.45/16.65      inference('simplify', [status(thm)], ['210'])).
% 16.45/16.65  thf('212', plain, (((sk_B) = (k1_xboole_0))),
% 16.45/16.65      inference('simplify', [status(thm)], ['200'])).
% 16.45/16.65  thf('213', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 16.45/16.65      inference('demod', [status(thm)], ['211', '212'])).
% 16.45/16.65  thf('214', plain,
% 16.45/16.65      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 16.45/16.65      inference('demod', [status(thm)], ['173', '181', '201', '213'])).
% 16.45/16.65  thf('215', plain,
% 16.45/16.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.45/16.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.45/16.65  thf('216', plain,
% 16.45/16.65      (![X46 : $i, X47 : $i, X48 : $i]:
% 16.45/16.65         ((r2_relset_1 @ X46 @ X47 @ X48 @ X48)
% 16.45/16.65          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 16.45/16.65      inference('simplify', [status(thm)], ['168'])).
% 16.45/16.65  thf('217', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 16.45/16.65      inference('sup-', [status(thm)], ['215', '216'])).
% 16.45/16.65  thf('218', plain, (((sk_A) = (k1_xboole_0))),
% 16.45/16.65      inference('demod', [status(thm)], ['166', '170'])).
% 16.45/16.65  thf('219', plain, (((sk_A) = (k1_xboole_0))),
% 16.45/16.65      inference('demod', [status(thm)], ['166', '170'])).
% 16.45/16.65  thf('220', plain, ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_B)),
% 16.45/16.65      inference('demod', [status(thm)], ['217', '218', '219'])).
% 16.45/16.65  thf('221', plain, (((sk_B) = (k1_xboole_0))),
% 16.45/16.65      inference('simplify', [status(thm)], ['200'])).
% 16.45/16.65  thf('222', plain, (((sk_B) = (k1_xboole_0))),
% 16.45/16.65      inference('simplify', [status(thm)], ['200'])).
% 16.45/16.65  thf('223', plain,
% 16.45/16.65      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 16.45/16.65      inference('demod', [status(thm)], ['220', '221', '222'])).
% 16.45/16.65  thf('224', plain, ($false), inference('demod', [status(thm)], ['214', '223'])).
% 16.45/16.65  
% 16.45/16.65  % SZS output end Refutation
% 16.45/16.65  
% 16.45/16.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
