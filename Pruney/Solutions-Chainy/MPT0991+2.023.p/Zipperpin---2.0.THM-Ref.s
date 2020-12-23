%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZWJKWs8x9Q

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:33 EST 2020

% Result     : Theorem 15.09s
% Output     : Refutation 15.09s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 147 expanded)
%              Number of leaves         :   37 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  832 (2685 expanded)
%              Number of equality atoms :   42 (  89 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t37_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ? [D: $i] :
              ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
              & ( v1_funct_2 @ D @ B @ A )
              & ( v1_funct_1 @ D ) )
          & ~ ( v2_funct_1 @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ? [D: $i] :
                ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
                & ( v1_funct_2 @ D @ B @ A )
                & ( v1_funct_1 @ D ) )
            & ~ ( v2_funct_1 @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_funct_2])).

thf('0',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_3 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('4',plain,(
    ! [X79: $i,X80: $i,X81: $i,X82: $i,X83: $i,X84: $i] :
      ( ~ ( m1_subset_1 @ X79 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X80 @ X81 ) ) )
      | ~ ( v1_funct_1 @ X79 )
      | ~ ( v1_funct_1 @ X82 )
      | ~ ( m1_subset_1 @ X82 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X83 @ X84 ) ) )
      | ( ( k1_partfun1 @ X80 @ X81 @ X83 @ X84 @ X79 @ X82 )
        = ( k5_relat_1 @ X79 @ X82 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_3 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_3 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D )
      = ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['1','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_3 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('14',plain,(
    ! [X71: $i,X72: $i,X73: $i,X74: $i,X75: $i,X76: $i] :
      ( ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X72 @ X73 ) ) )
      | ~ ( v1_funct_1 @ X71 )
      | ~ ( v1_funct_1 @ X74 )
      | ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X75 @ X76 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X72 @ X73 @ X75 @ X76 @ X71 @ X74 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X72 @ X76 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_3 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_3 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('22',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ( X59 = X62 )
      | ~ ( r2_relset_1 @ X60 @ X61 @ X59 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C_1 @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','24'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('26',plain,(
    ! [X78: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X78 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X78 @ X78 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,
    ( ( k5_relat_1 @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t53_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ~ ( v1_funct_1 @ X51 )
      | ( ( k5_relat_1 @ X52 @ X51 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X52 ) ) )
      | ( v2_funct_1 @ X52 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('29',plain,(
    ! [X85: $i] :
      ( ( k6_partfun1 @ X85 )
      = ( k6_relat_1 @ X85 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ~ ( v1_funct_1 @ X51 )
      | ( ( k5_relat_1 @ X52 @ X51 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X52 ) ) )
      | ( v2_funct_1 @ X52 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k1_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_3 ),
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

thf('33',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ~ ( v1_funct_2 @ X67 @ X65 @ X66 )
      | ( X65
        = ( k1_relset_1 @ X65 @ X66 @ X67 ) )
      | ~ ( zip_tseitin_1 @ X67 @ X66 @ X65 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X63: $i,X64: $i] :
      ( ( zip_tseitin_0 @ X63 @ X64 )
      | ( X63 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
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

thf('37',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ~ ( zip_tseitin_0 @ X68 @ X69 )
      | ( zip_tseitin_1 @ X70 @ X68 @ X69 )
      | ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X68 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('38',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B_3 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    sk_B_3 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_3 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( ( k1_relset_1 @ X57 @ X58 @ X56 )
        = ( k1_relat_1 @ X56 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_3 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['34','41','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('47',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( v1_relat_1 @ X53 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('48',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_3 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( v1_relat_1 @ X53 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','45','48','49','50','53'])).

thf('55',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZWJKWs8x9Q
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:22:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 15.09/15.30  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 15.09/15.30  % Solved by: fo/fo7.sh
% 15.09/15.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.09/15.30  % done 9921 iterations in 14.836s
% 15.09/15.30  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 15.09/15.30  % SZS output start Refutation
% 15.09/15.30  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 15.09/15.30  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 15.09/15.30  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 15.09/15.30  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 15.09/15.30  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 15.09/15.30  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 15.09/15.30  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 15.09/15.30  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 15.09/15.30  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 15.09/15.30  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 15.09/15.30  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 15.09/15.30  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 15.09/15.30  thf(sk_D_type, type, sk_D: $i).
% 15.09/15.30  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 15.09/15.30  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 15.09/15.30  thf(sk_A_type, type, sk_A: $i).
% 15.09/15.30  thf(sk_C_1_type, type, sk_C_1: $i).
% 15.09/15.30  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 15.09/15.30  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 15.09/15.30  thf(sk_B_3_type, type, sk_B_3: $i).
% 15.09/15.30  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.09/15.30  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 15.09/15.30  thf(t37_funct_2, conjecture,
% 15.09/15.30    (![A:$i,B:$i,C:$i]:
% 15.09/15.30     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 15.09/15.30         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.09/15.30       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 15.09/15.30            ( ?[D:$i]:
% 15.09/15.30              ( ( r2_relset_1 @
% 15.09/15.30                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 15.09/15.30                  ( k6_partfun1 @ A ) ) & 
% 15.09/15.30                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 15.09/15.30                ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 15.09/15.30            ( ~( v2_funct_1 @ C ) ) ) ) ))).
% 15.09/15.30  thf(zf_stmt_0, negated_conjecture,
% 15.09/15.30    (~( ![A:$i,B:$i,C:$i]:
% 15.09/15.30        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 15.09/15.30            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.09/15.30          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 15.09/15.30               ( ?[D:$i]:
% 15.09/15.30                 ( ( r2_relset_1 @
% 15.09/15.30                     A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 15.09/15.30                     ( k6_partfun1 @ A ) ) & 
% 15.09/15.30                   ( m1_subset_1 @
% 15.09/15.30                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 15.09/15.30                   ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 15.09/15.30               ( ~( v2_funct_1 @ C ) ) ) ) ) )),
% 15.09/15.30    inference('cnf.neg', [status(esa)], [t37_funct_2])).
% 15.09/15.30  thf('0', plain, (~ (v2_funct_1 @ sk_C_1)),
% 15.09/15.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.30  thf('1', plain,
% 15.09/15.30      ((r2_relset_1 @ sk_A @ sk_A @ 
% 15.09/15.30        (k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D) @ 
% 15.09/15.30        (k6_partfun1 @ sk_A))),
% 15.09/15.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.30  thf('2', plain,
% 15.09/15.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_3 @ sk_A)))),
% 15.09/15.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.30  thf('3', plain,
% 15.09/15.30      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 15.09/15.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.30  thf(redefinition_k1_partfun1, axiom,
% 15.09/15.30    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 15.09/15.30     ( ( ( v1_funct_1 @ E ) & 
% 15.09/15.30         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 15.09/15.30         ( v1_funct_1 @ F ) & 
% 15.09/15.30         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 15.09/15.30       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 15.09/15.30  thf('4', plain,
% 15.09/15.30      (![X79 : $i, X80 : $i, X81 : $i, X82 : $i, X83 : $i, X84 : $i]:
% 15.09/15.30         (~ (m1_subset_1 @ X79 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X80 @ X81)))
% 15.09/15.30          | ~ (v1_funct_1 @ X79)
% 15.09/15.30          | ~ (v1_funct_1 @ X82)
% 15.09/15.30          | ~ (m1_subset_1 @ X82 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X83 @ X84)))
% 15.09/15.30          | ((k1_partfun1 @ X80 @ X81 @ X83 @ X84 @ X79 @ X82)
% 15.09/15.30              = (k5_relat_1 @ X79 @ X82)))),
% 15.09/15.30      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 15.09/15.30  thf('5', plain,
% 15.09/15.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.09/15.30         (((k1_partfun1 @ sk_A @ sk_B_3 @ X2 @ X1 @ sk_C_1 @ X0)
% 15.09/15.30            = (k5_relat_1 @ sk_C_1 @ X0))
% 15.09/15.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 15.09/15.30          | ~ (v1_funct_1 @ X0)
% 15.09/15.30          | ~ (v1_funct_1 @ sk_C_1))),
% 15.09/15.30      inference('sup-', [status(thm)], ['3', '4'])).
% 15.09/15.30  thf('6', plain, ((v1_funct_1 @ sk_C_1)),
% 15.09/15.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.30  thf('7', plain,
% 15.09/15.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.09/15.30         (((k1_partfun1 @ sk_A @ sk_B_3 @ X2 @ X1 @ sk_C_1 @ X0)
% 15.09/15.30            = (k5_relat_1 @ sk_C_1 @ X0))
% 15.09/15.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 15.09/15.30          | ~ (v1_funct_1 @ X0))),
% 15.09/15.30      inference('demod', [status(thm)], ['5', '6'])).
% 15.09/15.30  thf('8', plain,
% 15.09/15.30      ((~ (v1_funct_1 @ sk_D)
% 15.09/15.30        | ((k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D)
% 15.09/15.30            = (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 15.09/15.30      inference('sup-', [status(thm)], ['2', '7'])).
% 15.09/15.30  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 15.09/15.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.30  thf('10', plain,
% 15.09/15.30      (((k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D)
% 15.09/15.30         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 15.09/15.30      inference('demod', [status(thm)], ['8', '9'])).
% 15.09/15.30  thf('11', plain,
% 15.09/15.30      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 15.09/15.30        (k6_partfun1 @ sk_A))),
% 15.09/15.30      inference('demod', [status(thm)], ['1', '10'])).
% 15.09/15.30  thf('12', plain,
% 15.09/15.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_3 @ sk_A)))),
% 15.09/15.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.30  thf('13', plain,
% 15.09/15.30      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 15.09/15.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.30  thf(dt_k1_partfun1, axiom,
% 15.09/15.30    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 15.09/15.30     ( ( ( v1_funct_1 @ E ) & 
% 15.09/15.30         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 15.09/15.30         ( v1_funct_1 @ F ) & 
% 15.09/15.30         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 15.09/15.30       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 15.09/15.30         ( m1_subset_1 @
% 15.09/15.30           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 15.09/15.30           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 15.09/15.30  thf('14', plain,
% 15.09/15.30      (![X71 : $i, X72 : $i, X73 : $i, X74 : $i, X75 : $i, X76 : $i]:
% 15.09/15.30         (~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X72 @ X73)))
% 15.09/15.30          | ~ (v1_funct_1 @ X71)
% 15.09/15.30          | ~ (v1_funct_1 @ X74)
% 15.09/15.30          | ~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X75 @ X76)))
% 15.09/15.30          | (m1_subset_1 @ (k1_partfun1 @ X72 @ X73 @ X75 @ X76 @ X71 @ X74) @ 
% 15.09/15.30             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X72 @ X76))))),
% 15.09/15.30      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 15.09/15.30  thf('15', plain,
% 15.09/15.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.09/15.30         ((m1_subset_1 @ 
% 15.09/15.30           (k1_partfun1 @ sk_A @ sk_B_3 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 15.09/15.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 15.09/15.30          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 15.09/15.30          | ~ (v1_funct_1 @ X1)
% 15.09/15.30          | ~ (v1_funct_1 @ sk_C_1))),
% 15.09/15.30      inference('sup-', [status(thm)], ['13', '14'])).
% 15.09/15.30  thf('16', plain, ((v1_funct_1 @ sk_C_1)),
% 15.09/15.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.30  thf('17', plain,
% 15.09/15.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.09/15.30         ((m1_subset_1 @ 
% 15.09/15.30           (k1_partfun1 @ sk_A @ sk_B_3 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 15.09/15.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 15.09/15.30          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 15.09/15.30          | ~ (v1_funct_1 @ X1))),
% 15.09/15.30      inference('demod', [status(thm)], ['15', '16'])).
% 15.09/15.30  thf('18', plain,
% 15.09/15.30      ((~ (v1_funct_1 @ sk_D)
% 15.09/15.30        | (m1_subset_1 @ 
% 15.09/15.30           (k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D) @ 
% 15.09/15.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 15.09/15.30      inference('sup-', [status(thm)], ['12', '17'])).
% 15.09/15.30  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 15.09/15.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.30  thf('20', plain,
% 15.09/15.30      ((m1_subset_1 @ 
% 15.09/15.30        (k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D) @ 
% 15.09/15.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 15.09/15.30      inference('demod', [status(thm)], ['18', '19'])).
% 15.09/15.30  thf('21', plain,
% 15.09/15.30      (((k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D)
% 15.09/15.30         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 15.09/15.30      inference('demod', [status(thm)], ['8', '9'])).
% 15.09/15.30  thf('22', plain,
% 15.09/15.30      ((m1_subset_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 15.09/15.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 15.09/15.30      inference('demod', [status(thm)], ['20', '21'])).
% 15.09/15.30  thf(redefinition_r2_relset_1, axiom,
% 15.09/15.30    (![A:$i,B:$i,C:$i,D:$i]:
% 15.09/15.30     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 15.09/15.30         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.09/15.30       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 15.09/15.30  thf('23', plain,
% 15.09/15.30      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 15.09/15.30         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 15.09/15.30          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 15.09/15.30          | ((X59) = (X62))
% 15.09/15.30          | ~ (r2_relset_1 @ X60 @ X61 @ X59 @ X62))),
% 15.09/15.30      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 15.09/15.30  thf('24', plain,
% 15.09/15.30      (![X0 : $i]:
% 15.09/15.30         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_D) @ X0)
% 15.09/15.30          | ((k5_relat_1 @ sk_C_1 @ sk_D) = (X0))
% 15.09/15.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 15.09/15.30      inference('sup-', [status(thm)], ['22', '23'])).
% 15.09/15.30  thf('25', plain,
% 15.09/15.30      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 15.09/15.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 15.09/15.30        | ((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A)))),
% 15.09/15.30      inference('sup-', [status(thm)], ['11', '24'])).
% 15.09/15.30  thf(dt_k6_partfun1, axiom,
% 15.09/15.30    (![A:$i]:
% 15.09/15.30     ( ( m1_subset_1 @
% 15.09/15.30         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 15.09/15.30       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 15.09/15.30  thf('26', plain,
% 15.09/15.30      (![X78 : $i]:
% 15.09/15.30         (m1_subset_1 @ (k6_partfun1 @ X78) @ 
% 15.09/15.30          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X78 @ X78)))),
% 15.09/15.30      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 15.09/15.30  thf('27', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A))),
% 15.09/15.30      inference('demod', [status(thm)], ['25', '26'])).
% 15.09/15.30  thf(t53_funct_1, axiom,
% 15.09/15.30    (![A:$i]:
% 15.09/15.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 15.09/15.30       ( ( ?[B:$i]:
% 15.09/15.30           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 15.09/15.30             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 15.09/15.30         ( v2_funct_1 @ A ) ) ))).
% 15.09/15.30  thf('28', plain,
% 15.09/15.30      (![X51 : $i, X52 : $i]:
% 15.09/15.30         (~ (v1_relat_1 @ X51)
% 15.09/15.30          | ~ (v1_funct_1 @ X51)
% 15.09/15.30          | ((k5_relat_1 @ X52 @ X51) != (k6_relat_1 @ (k1_relat_1 @ X52)))
% 15.09/15.30          | (v2_funct_1 @ X52)
% 15.09/15.30          | ~ (v1_funct_1 @ X52)
% 15.09/15.30          | ~ (v1_relat_1 @ X52))),
% 15.09/15.30      inference('cnf', [status(esa)], [t53_funct_1])).
% 15.09/15.30  thf(redefinition_k6_partfun1, axiom,
% 15.09/15.30    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 15.09/15.30  thf('29', plain, (![X85 : $i]: ((k6_partfun1 @ X85) = (k6_relat_1 @ X85))),
% 15.09/15.30      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 15.09/15.30  thf('30', plain,
% 15.09/15.30      (![X51 : $i, X52 : $i]:
% 15.09/15.30         (~ (v1_relat_1 @ X51)
% 15.09/15.30          | ~ (v1_funct_1 @ X51)
% 15.09/15.30          | ((k5_relat_1 @ X52 @ X51) != (k6_partfun1 @ (k1_relat_1 @ X52)))
% 15.09/15.30          | (v2_funct_1 @ X52)
% 15.09/15.30          | ~ (v1_funct_1 @ X52)
% 15.09/15.30          | ~ (v1_relat_1 @ X52))),
% 15.09/15.30      inference('demod', [status(thm)], ['28', '29'])).
% 15.09/15.30  thf('31', plain,
% 15.09/15.30      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k1_relat_1 @ sk_C_1)))
% 15.09/15.30        | ~ (v1_relat_1 @ sk_C_1)
% 15.09/15.30        | ~ (v1_funct_1 @ sk_C_1)
% 15.09/15.30        | (v2_funct_1 @ sk_C_1)
% 15.09/15.30        | ~ (v1_funct_1 @ sk_D)
% 15.09/15.30        | ~ (v1_relat_1 @ sk_D))),
% 15.09/15.30      inference('sup-', [status(thm)], ['27', '30'])).
% 15.09/15.30  thf('32', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_3)),
% 15.09/15.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.30  thf(d1_funct_2, axiom,
% 15.09/15.30    (![A:$i,B:$i,C:$i]:
% 15.09/15.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.09/15.30       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.09/15.30           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 15.09/15.30             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 15.09/15.30         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.09/15.30           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 15.09/15.30             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 15.09/15.30  thf(zf_stmt_1, axiom,
% 15.09/15.30    (![C:$i,B:$i,A:$i]:
% 15.09/15.30     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 15.09/15.30       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 15.09/15.30  thf('33', plain,
% 15.09/15.30      (![X65 : $i, X66 : $i, X67 : $i]:
% 15.09/15.30         (~ (v1_funct_2 @ X67 @ X65 @ X66)
% 15.09/15.30          | ((X65) = (k1_relset_1 @ X65 @ X66 @ X67))
% 15.09/15.30          | ~ (zip_tseitin_1 @ X67 @ X66 @ X65))),
% 15.09/15.30      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.09/15.30  thf('34', plain,
% 15.09/15.30      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_3 @ sk_A)
% 15.09/15.30        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 15.09/15.30      inference('sup-', [status(thm)], ['32', '33'])).
% 15.09/15.30  thf(zf_stmt_2, axiom,
% 15.09/15.30    (![B:$i,A:$i]:
% 15.09/15.30     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.09/15.30       ( zip_tseitin_0 @ B @ A ) ))).
% 15.09/15.30  thf('35', plain,
% 15.09/15.30      (![X63 : $i, X64 : $i]:
% 15.09/15.30         ((zip_tseitin_0 @ X63 @ X64) | ((X63) = (k1_xboole_0)))),
% 15.09/15.30      inference('cnf', [status(esa)], [zf_stmt_2])).
% 15.09/15.30  thf('36', plain,
% 15.09/15.30      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 15.09/15.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.30  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 15.09/15.31  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 15.09/15.31  thf(zf_stmt_5, axiom,
% 15.09/15.31    (![A:$i,B:$i,C:$i]:
% 15.09/15.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.09/15.31       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 15.09/15.31         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.09/15.31           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 15.09/15.31             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 15.09/15.31  thf('37', plain,
% 15.09/15.31      (![X68 : $i, X69 : $i, X70 : $i]:
% 15.09/15.31         (~ (zip_tseitin_0 @ X68 @ X69)
% 15.09/15.31          | (zip_tseitin_1 @ X70 @ X68 @ X69)
% 15.09/15.31          | ~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X68))))),
% 15.09/15.31      inference('cnf', [status(esa)], [zf_stmt_5])).
% 15.09/15.31  thf('38', plain,
% 15.09/15.31      (((zip_tseitin_1 @ sk_C_1 @ sk_B_3 @ sk_A)
% 15.09/15.31        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A))),
% 15.09/15.31      inference('sup-', [status(thm)], ['36', '37'])).
% 15.09/15.31  thf('39', plain,
% 15.09/15.31      ((((sk_B_3) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B_3 @ sk_A))),
% 15.09/15.31      inference('sup-', [status(thm)], ['35', '38'])).
% 15.09/15.31  thf('40', plain, (((sk_B_3) != (k1_xboole_0))),
% 15.09/15.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.31  thf('41', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_3 @ sk_A)),
% 15.09/15.31      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 15.09/15.31  thf('42', plain,
% 15.09/15.31      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 15.09/15.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.31  thf(redefinition_k1_relset_1, axiom,
% 15.09/15.31    (![A:$i,B:$i,C:$i]:
% 15.09/15.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.09/15.31       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 15.09/15.31  thf('43', plain,
% 15.09/15.31      (![X56 : $i, X57 : $i, X58 : $i]:
% 15.09/15.31         (((k1_relset_1 @ X57 @ X58 @ X56) = (k1_relat_1 @ X56))
% 15.09/15.31          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58))))),
% 15.09/15.31      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.09/15.31  thf('44', plain,
% 15.09/15.31      (((k1_relset_1 @ sk_A @ sk_B_3 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 15.09/15.31      inference('sup-', [status(thm)], ['42', '43'])).
% 15.09/15.31  thf('45', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 15.09/15.31      inference('demod', [status(thm)], ['34', '41', '44'])).
% 15.09/15.31  thf('46', plain,
% 15.09/15.31      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 15.09/15.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.31  thf(cc1_relset_1, axiom,
% 15.09/15.31    (![A:$i,B:$i,C:$i]:
% 15.09/15.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.09/15.31       ( v1_relat_1 @ C ) ))).
% 15.09/15.31  thf('47', plain,
% 15.09/15.31      (![X53 : $i, X54 : $i, X55 : $i]:
% 15.09/15.31         ((v1_relat_1 @ X53)
% 15.09/15.31          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55))))),
% 15.09/15.31      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.09/15.31  thf('48', plain, ((v1_relat_1 @ sk_C_1)),
% 15.09/15.31      inference('sup-', [status(thm)], ['46', '47'])).
% 15.09/15.31  thf('49', plain, ((v1_funct_1 @ sk_C_1)),
% 15.09/15.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.31  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 15.09/15.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.31  thf('51', plain,
% 15.09/15.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_3 @ sk_A)))),
% 15.09/15.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.09/15.31  thf('52', plain,
% 15.09/15.31      (![X53 : $i, X54 : $i, X55 : $i]:
% 15.09/15.31         ((v1_relat_1 @ X53)
% 15.09/15.31          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55))))),
% 15.09/15.31      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.09/15.31  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 15.09/15.31      inference('sup-', [status(thm)], ['51', '52'])).
% 15.09/15.31  thf('54', plain,
% 15.09/15.31      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A)) | (v2_funct_1 @ sk_C_1))),
% 15.09/15.31      inference('demod', [status(thm)], ['31', '45', '48', '49', '50', '53'])).
% 15.09/15.31  thf('55', plain, ((v2_funct_1 @ sk_C_1)),
% 15.09/15.31      inference('simplify', [status(thm)], ['54'])).
% 15.09/15.31  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 15.09/15.31  
% 15.09/15.31  % SZS output end Refutation
% 15.09/15.31  
% 15.09/15.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
