%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.58557e91gr

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:33 EST 2020

% Result     : Theorem 17.12s
% Output     : Refutation 17.12s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 149 expanded)
%              Number of leaves         :   36 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  840 (2698 expanded)
%              Number of equality atoms :   43 (  91 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

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
    ! [X78: $i,X79: $i,X80: $i,X81: $i,X82: $i,X83: $i] :
      ( ~ ( m1_subset_1 @ X78 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X79 @ X80 ) ) )
      | ~ ( v1_funct_1 @ X78 )
      | ~ ( v1_funct_1 @ X81 )
      | ~ ( m1_subset_1 @ X81 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X82 @ X83 ) ) )
      | ( ( k1_partfun1 @ X79 @ X80 @ X82 @ X83 @ X78 @ X81 )
        = ( k5_relat_1 @ X78 @ X81 ) ) ) ),
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
    ! [X72: $i,X73: $i,X74: $i,X75: $i,X76: $i,X77: $i] :
      ( ~ ( m1_subset_1 @ X72 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X73 @ X74 ) ) )
      | ~ ( v1_funct_1 @ X72 )
      | ~ ( v1_funct_1 @ X75 )
      | ~ ( m1_subset_1 @ X75 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X76 @ X77 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X73 @ X74 @ X76 @ X77 @ X72 @ X75 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X73 @ X77 ) ) ) ) ),
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

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('26',plain,(
    ! [X63: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X63 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('27',plain,(
    ! [X84: $i] :
      ( ( k6_partfun1 @ X84 )
      = ( k6_relat_1 @ X84 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X63: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X63 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X63 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k5_relat_1 @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

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

thf('30',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ~ ( v1_funct_1 @ X51 )
      | ( ( k5_relat_1 @ X52 @ X51 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X52 ) ) )
      | ( v2_funct_1 @ X52 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf('31',plain,(
    ! [X84: $i] :
      ( ( k6_partfun1 @ X84 )
      = ( k6_relat_1 @ X84 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('32',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ~ ( v1_funct_1 @ X51 )
      | ( ( k5_relat_1 @ X52 @ X51 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X52 ) ) )
      | ( v2_funct_1 @ X52 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k1_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ~ ( v1_funct_2 @ X68 @ X66 @ X67 )
      | ( X66
        = ( k1_relset_1 @ X66 @ X67 @ X68 ) )
      | ~ ( zip_tseitin_1 @ X68 @ X67 @ X66 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('36',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X64: $i,X65: $i] :
      ( ( zip_tseitin_0 @ X64 @ X65 )
      | ( X64 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X69: $i,X70: $i,X71: $i] :
      ( ~ ( zip_tseitin_0 @ X69 @ X70 )
      | ( zip_tseitin_1 @ X71 @ X69 @ X70 )
      | ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X70 @ X69 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('40',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B_3 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    sk_B_3 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_3 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('45',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( ( k1_relset_1 @ X57 @ X58 @ X56 )
        = ( k1_relat_1 @ X56 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('46',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_3 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['36','43','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('49',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( v1_relat_1 @ X53 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('50',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_3 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( v1_relat_1 @ X53 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('55',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['33','47','50','51','52','55'])).

thf('57',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.58557e91gr
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:37:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 17.12/17.32  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.12/17.32  % Solved by: fo/fo7.sh
% 17.12/17.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.12/17.32  % done 9921 iterations in 16.821s
% 17.12/17.32  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.12/17.32  % SZS output start Refutation
% 17.12/17.32  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 17.12/17.32  thf(sk_B_3_type, type, sk_B_3: $i).
% 17.12/17.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 17.12/17.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 17.12/17.32  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 17.12/17.32  thf(sk_A_type, type, sk_A: $i).
% 17.12/17.32  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 17.12/17.32  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 17.12/17.32  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 17.12/17.32  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 17.12/17.32  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 17.12/17.32  thf(sk_C_1_type, type, sk_C_1: $i).
% 17.12/17.32  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 17.12/17.32  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 17.12/17.32  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 17.12/17.32  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 17.12/17.32  thf(sk_D_type, type, sk_D: $i).
% 17.12/17.32  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 17.12/17.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 17.12/17.32  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 17.12/17.32  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 17.12/17.32  thf(t37_funct_2, conjecture,
% 17.12/17.32    (![A:$i,B:$i,C:$i]:
% 17.12/17.32     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 17.12/17.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 17.12/17.32       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 17.12/17.32            ( ?[D:$i]:
% 17.12/17.32              ( ( r2_relset_1 @
% 17.12/17.32                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 17.12/17.32                  ( k6_partfun1 @ A ) ) & 
% 17.12/17.32                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 17.12/17.32                ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 17.12/17.32            ( ~( v2_funct_1 @ C ) ) ) ) ))).
% 17.12/17.32  thf(zf_stmt_0, negated_conjecture,
% 17.12/17.32    (~( ![A:$i,B:$i,C:$i]:
% 17.12/17.32        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 17.12/17.32            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 17.12/17.32          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 17.12/17.32               ( ?[D:$i]:
% 17.12/17.32                 ( ( r2_relset_1 @
% 17.12/17.32                     A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 17.12/17.32                     ( k6_partfun1 @ A ) ) & 
% 17.12/17.32                   ( m1_subset_1 @
% 17.12/17.32                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 17.12/17.32                   ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 17.12/17.32               ( ~( v2_funct_1 @ C ) ) ) ) ) )),
% 17.12/17.32    inference('cnf.neg', [status(esa)], [t37_funct_2])).
% 17.12/17.32  thf('0', plain, (~ (v2_funct_1 @ sk_C_1)),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf('1', plain,
% 17.12/17.32      ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.12/17.32        (k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D) @ 
% 17.12/17.32        (k6_partfun1 @ sk_A))),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf('2', plain,
% 17.12/17.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_3 @ sk_A)))),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf('3', plain,
% 17.12/17.32      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf(redefinition_k1_partfun1, axiom,
% 17.12/17.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 17.12/17.32     ( ( ( v1_funct_1 @ E ) & 
% 17.12/17.32         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 17.12/17.32         ( v1_funct_1 @ F ) & 
% 17.12/17.32         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 17.12/17.32       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 17.12/17.32  thf('4', plain,
% 17.12/17.32      (![X78 : $i, X79 : $i, X80 : $i, X81 : $i, X82 : $i, X83 : $i]:
% 17.12/17.32         (~ (m1_subset_1 @ X78 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X79 @ X80)))
% 17.12/17.32          | ~ (v1_funct_1 @ X78)
% 17.12/17.32          | ~ (v1_funct_1 @ X81)
% 17.12/17.32          | ~ (m1_subset_1 @ X81 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X82 @ X83)))
% 17.12/17.32          | ((k1_partfun1 @ X79 @ X80 @ X82 @ X83 @ X78 @ X81)
% 17.12/17.32              = (k5_relat_1 @ X78 @ X81)))),
% 17.12/17.32      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 17.12/17.32  thf('5', plain,
% 17.12/17.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.12/17.32         (((k1_partfun1 @ sk_A @ sk_B_3 @ X2 @ X1 @ sk_C_1 @ X0)
% 17.12/17.32            = (k5_relat_1 @ sk_C_1 @ X0))
% 17.12/17.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 17.12/17.32          | ~ (v1_funct_1 @ X0)
% 17.12/17.32          | ~ (v1_funct_1 @ sk_C_1))),
% 17.12/17.32      inference('sup-', [status(thm)], ['3', '4'])).
% 17.12/17.32  thf('6', plain, ((v1_funct_1 @ sk_C_1)),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf('7', plain,
% 17.12/17.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.12/17.32         (((k1_partfun1 @ sk_A @ sk_B_3 @ X2 @ X1 @ sk_C_1 @ X0)
% 17.12/17.32            = (k5_relat_1 @ sk_C_1 @ X0))
% 17.12/17.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 17.12/17.32          | ~ (v1_funct_1 @ X0))),
% 17.12/17.32      inference('demod', [status(thm)], ['5', '6'])).
% 17.12/17.32  thf('8', plain,
% 17.12/17.32      ((~ (v1_funct_1 @ sk_D)
% 17.12/17.32        | ((k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D)
% 17.12/17.32            = (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 17.12/17.32      inference('sup-', [status(thm)], ['2', '7'])).
% 17.12/17.32  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf('10', plain,
% 17.12/17.32      (((k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D)
% 17.12/17.32         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 17.12/17.32      inference('demod', [status(thm)], ['8', '9'])).
% 17.12/17.32  thf('11', plain,
% 17.12/17.32      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 17.12/17.32        (k6_partfun1 @ sk_A))),
% 17.12/17.32      inference('demod', [status(thm)], ['1', '10'])).
% 17.12/17.32  thf('12', plain,
% 17.12/17.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_3 @ sk_A)))),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf('13', plain,
% 17.12/17.32      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf(dt_k1_partfun1, axiom,
% 17.12/17.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 17.12/17.32     ( ( ( v1_funct_1 @ E ) & 
% 17.12/17.32         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 17.12/17.32         ( v1_funct_1 @ F ) & 
% 17.12/17.32         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 17.12/17.32       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 17.12/17.32         ( m1_subset_1 @
% 17.12/17.32           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 17.12/17.32           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 17.12/17.32  thf('14', plain,
% 17.12/17.32      (![X72 : $i, X73 : $i, X74 : $i, X75 : $i, X76 : $i, X77 : $i]:
% 17.12/17.32         (~ (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X73 @ X74)))
% 17.12/17.32          | ~ (v1_funct_1 @ X72)
% 17.12/17.32          | ~ (v1_funct_1 @ X75)
% 17.12/17.32          | ~ (m1_subset_1 @ X75 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X76 @ X77)))
% 17.12/17.32          | (m1_subset_1 @ (k1_partfun1 @ X73 @ X74 @ X76 @ X77 @ X72 @ X75) @ 
% 17.12/17.32             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X73 @ X77))))),
% 17.12/17.32      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 17.12/17.32  thf('15', plain,
% 17.12/17.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.12/17.32         ((m1_subset_1 @ 
% 17.12/17.32           (k1_partfun1 @ sk_A @ sk_B_3 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 17.12/17.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 17.12/17.32          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 17.12/17.32          | ~ (v1_funct_1 @ X1)
% 17.12/17.32          | ~ (v1_funct_1 @ sk_C_1))),
% 17.12/17.32      inference('sup-', [status(thm)], ['13', '14'])).
% 17.12/17.32  thf('16', plain, ((v1_funct_1 @ sk_C_1)),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf('17', plain,
% 17.12/17.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.12/17.32         ((m1_subset_1 @ 
% 17.12/17.32           (k1_partfun1 @ sk_A @ sk_B_3 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 17.12/17.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 17.12/17.32          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 17.12/17.32          | ~ (v1_funct_1 @ X1))),
% 17.12/17.32      inference('demod', [status(thm)], ['15', '16'])).
% 17.12/17.32  thf('18', plain,
% 17.12/17.32      ((~ (v1_funct_1 @ sk_D)
% 17.12/17.32        | (m1_subset_1 @ 
% 17.12/17.32           (k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D) @ 
% 17.12/17.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 17.12/17.32      inference('sup-', [status(thm)], ['12', '17'])).
% 17.12/17.32  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf('20', plain,
% 17.12/17.32      ((m1_subset_1 @ 
% 17.12/17.32        (k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D) @ 
% 17.12/17.32        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.12/17.32      inference('demod', [status(thm)], ['18', '19'])).
% 17.12/17.32  thf('21', plain,
% 17.12/17.32      (((k1_partfun1 @ sk_A @ sk_B_3 @ sk_B_3 @ sk_A @ sk_C_1 @ sk_D)
% 17.12/17.32         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 17.12/17.32      inference('demod', [status(thm)], ['8', '9'])).
% 17.12/17.32  thf('22', plain,
% 17.12/17.32      ((m1_subset_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 17.12/17.32        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.12/17.32      inference('demod', [status(thm)], ['20', '21'])).
% 17.12/17.32  thf(redefinition_r2_relset_1, axiom,
% 17.12/17.32    (![A:$i,B:$i,C:$i,D:$i]:
% 17.12/17.32     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 17.12/17.32         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 17.12/17.32       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 17.12/17.32  thf('23', plain,
% 17.12/17.32      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 17.12/17.32         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 17.12/17.32          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 17.12/17.32          | ((X59) = (X62))
% 17.12/17.32          | ~ (r2_relset_1 @ X60 @ X61 @ X59 @ X62))),
% 17.12/17.32      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 17.12/17.32  thf('24', plain,
% 17.12/17.32      (![X0 : $i]:
% 17.12/17.32         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_D) @ X0)
% 17.12/17.32          | ((k5_relat_1 @ sk_C_1 @ sk_D) = (X0))
% 17.12/17.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 17.12/17.32      inference('sup-', [status(thm)], ['22', '23'])).
% 17.12/17.32  thf('25', plain,
% 17.12/17.32      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 17.12/17.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 17.12/17.32        | ((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A)))),
% 17.12/17.32      inference('sup-', [status(thm)], ['11', '24'])).
% 17.12/17.32  thf(t29_relset_1, axiom,
% 17.12/17.32    (![A:$i]:
% 17.12/17.32     ( m1_subset_1 @
% 17.12/17.32       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 17.12/17.32  thf('26', plain,
% 17.12/17.32      (![X63 : $i]:
% 17.12/17.32         (m1_subset_1 @ (k6_relat_1 @ X63) @ 
% 17.12/17.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X63)))),
% 17.12/17.32      inference('cnf', [status(esa)], [t29_relset_1])).
% 17.12/17.32  thf(redefinition_k6_partfun1, axiom,
% 17.12/17.32    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 17.12/17.32  thf('27', plain, (![X84 : $i]: ((k6_partfun1 @ X84) = (k6_relat_1 @ X84))),
% 17.12/17.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 17.12/17.32  thf('28', plain,
% 17.12/17.32      (![X63 : $i]:
% 17.12/17.32         (m1_subset_1 @ (k6_partfun1 @ X63) @ 
% 17.12/17.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X63)))),
% 17.12/17.32      inference('demod', [status(thm)], ['26', '27'])).
% 17.12/17.32  thf('29', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A))),
% 17.12/17.32      inference('demod', [status(thm)], ['25', '28'])).
% 17.12/17.32  thf(t53_funct_1, axiom,
% 17.12/17.32    (![A:$i]:
% 17.12/17.32     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 17.12/17.32       ( ( ?[B:$i]:
% 17.12/17.32           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 17.12/17.32             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 17.12/17.32         ( v2_funct_1 @ A ) ) ))).
% 17.12/17.32  thf('30', plain,
% 17.12/17.32      (![X51 : $i, X52 : $i]:
% 17.12/17.32         (~ (v1_relat_1 @ X51)
% 17.12/17.32          | ~ (v1_funct_1 @ X51)
% 17.12/17.32          | ((k5_relat_1 @ X52 @ X51) != (k6_relat_1 @ (k1_relat_1 @ X52)))
% 17.12/17.32          | (v2_funct_1 @ X52)
% 17.12/17.32          | ~ (v1_funct_1 @ X52)
% 17.12/17.32          | ~ (v1_relat_1 @ X52))),
% 17.12/17.32      inference('cnf', [status(esa)], [t53_funct_1])).
% 17.12/17.32  thf('31', plain, (![X84 : $i]: ((k6_partfun1 @ X84) = (k6_relat_1 @ X84))),
% 17.12/17.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 17.12/17.32  thf('32', plain,
% 17.12/17.32      (![X51 : $i, X52 : $i]:
% 17.12/17.32         (~ (v1_relat_1 @ X51)
% 17.12/17.32          | ~ (v1_funct_1 @ X51)
% 17.12/17.32          | ((k5_relat_1 @ X52 @ X51) != (k6_partfun1 @ (k1_relat_1 @ X52)))
% 17.12/17.32          | (v2_funct_1 @ X52)
% 17.12/17.32          | ~ (v1_funct_1 @ X52)
% 17.12/17.32          | ~ (v1_relat_1 @ X52))),
% 17.12/17.32      inference('demod', [status(thm)], ['30', '31'])).
% 17.12/17.32  thf('33', plain,
% 17.12/17.32      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k1_relat_1 @ sk_C_1)))
% 17.12/17.32        | ~ (v1_relat_1 @ sk_C_1)
% 17.12/17.32        | ~ (v1_funct_1 @ sk_C_1)
% 17.12/17.32        | (v2_funct_1 @ sk_C_1)
% 17.12/17.32        | ~ (v1_funct_1 @ sk_D)
% 17.12/17.32        | ~ (v1_relat_1 @ sk_D))),
% 17.12/17.32      inference('sup-', [status(thm)], ['29', '32'])).
% 17.12/17.32  thf('34', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_3)),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf(d1_funct_2, axiom,
% 17.12/17.32    (![A:$i,B:$i,C:$i]:
% 17.12/17.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.12/17.32       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 17.12/17.32           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 17.12/17.32             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 17.12/17.32         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 17.12/17.32           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 17.12/17.32             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 17.12/17.32  thf(zf_stmt_1, axiom,
% 17.12/17.32    (![C:$i,B:$i,A:$i]:
% 17.12/17.32     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 17.12/17.32       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 17.12/17.32  thf('35', plain,
% 17.12/17.32      (![X66 : $i, X67 : $i, X68 : $i]:
% 17.12/17.32         (~ (v1_funct_2 @ X68 @ X66 @ X67)
% 17.12/17.32          | ((X66) = (k1_relset_1 @ X66 @ X67 @ X68))
% 17.12/17.32          | ~ (zip_tseitin_1 @ X68 @ X67 @ X66))),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_1])).
% 17.12/17.32  thf('36', plain,
% 17.12/17.32      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_3 @ sk_A)
% 17.12/17.32        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 17.12/17.32      inference('sup-', [status(thm)], ['34', '35'])).
% 17.12/17.32  thf(zf_stmt_2, axiom,
% 17.12/17.32    (![B:$i,A:$i]:
% 17.12/17.32     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 17.12/17.32       ( zip_tseitin_0 @ B @ A ) ))).
% 17.12/17.32  thf('37', plain,
% 17.12/17.32      (![X64 : $i, X65 : $i]:
% 17.12/17.32         ((zip_tseitin_0 @ X64 @ X65) | ((X64) = (k1_xboole_0)))),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_2])).
% 17.12/17.32  thf('38', plain,
% 17.12/17.32      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 17.12/17.32  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 17.12/17.32  thf(zf_stmt_5, axiom,
% 17.12/17.32    (![A:$i,B:$i,C:$i]:
% 17.12/17.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.12/17.32       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 17.12/17.32         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 17.12/17.32           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 17.12/17.32             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 17.12/17.32  thf('39', plain,
% 17.12/17.32      (![X69 : $i, X70 : $i, X71 : $i]:
% 17.12/17.32         (~ (zip_tseitin_0 @ X69 @ X70)
% 17.12/17.32          | (zip_tseitin_1 @ X71 @ X69 @ X70)
% 17.12/17.32          | ~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X70 @ X69))))),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_5])).
% 17.12/17.32  thf('40', plain,
% 17.12/17.32      (((zip_tseitin_1 @ sk_C_1 @ sk_B_3 @ sk_A)
% 17.12/17.32        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A))),
% 17.12/17.32      inference('sup-', [status(thm)], ['38', '39'])).
% 17.12/17.32  thf('41', plain,
% 17.12/17.32      ((((sk_B_3) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B_3 @ sk_A))),
% 17.12/17.32      inference('sup-', [status(thm)], ['37', '40'])).
% 17.12/17.32  thf('42', plain, (((sk_B_3) != (k1_xboole_0))),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf('43', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_3 @ sk_A)),
% 17.12/17.32      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 17.12/17.32  thf('44', plain,
% 17.12/17.32      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf(redefinition_k1_relset_1, axiom,
% 17.12/17.32    (![A:$i,B:$i,C:$i]:
% 17.12/17.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.12/17.32       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 17.12/17.32  thf('45', plain,
% 17.12/17.32      (![X56 : $i, X57 : $i, X58 : $i]:
% 17.12/17.32         (((k1_relset_1 @ X57 @ X58 @ X56) = (k1_relat_1 @ X56))
% 17.12/17.32          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58))))),
% 17.12/17.32      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 17.12/17.32  thf('46', plain,
% 17.12/17.32      (((k1_relset_1 @ sk_A @ sk_B_3 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 17.12/17.32      inference('sup-', [status(thm)], ['44', '45'])).
% 17.12/17.32  thf('47', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 17.12/17.32      inference('demod', [status(thm)], ['36', '43', '46'])).
% 17.12/17.32  thf('48', plain,
% 17.12/17.32      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf(cc1_relset_1, axiom,
% 17.12/17.32    (![A:$i,B:$i,C:$i]:
% 17.12/17.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.12/17.32       ( v1_relat_1 @ C ) ))).
% 17.12/17.32  thf('49', plain,
% 17.12/17.32      (![X53 : $i, X54 : $i, X55 : $i]:
% 17.12/17.32         ((v1_relat_1 @ X53)
% 17.12/17.32          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55))))),
% 17.12/17.32      inference('cnf', [status(esa)], [cc1_relset_1])).
% 17.12/17.32  thf('50', plain, ((v1_relat_1 @ sk_C_1)),
% 17.12/17.32      inference('sup-', [status(thm)], ['48', '49'])).
% 17.12/17.32  thf('51', plain, ((v1_funct_1 @ sk_C_1)),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf('53', plain,
% 17.12/17.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_3 @ sk_A)))),
% 17.12/17.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.12/17.32  thf('54', plain,
% 17.12/17.32      (![X53 : $i, X54 : $i, X55 : $i]:
% 17.12/17.32         ((v1_relat_1 @ X53)
% 17.12/17.32          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55))))),
% 17.12/17.32      inference('cnf', [status(esa)], [cc1_relset_1])).
% 17.12/17.32  thf('55', plain, ((v1_relat_1 @ sk_D)),
% 17.12/17.32      inference('sup-', [status(thm)], ['53', '54'])).
% 17.12/17.32  thf('56', plain,
% 17.12/17.32      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A)) | (v2_funct_1 @ sk_C_1))),
% 17.12/17.32      inference('demod', [status(thm)], ['33', '47', '50', '51', '52', '55'])).
% 17.12/17.32  thf('57', plain, ((v2_funct_1 @ sk_C_1)),
% 17.12/17.32      inference('simplify', [status(thm)], ['56'])).
% 17.12/17.32  thf('58', plain, ($false), inference('demod', [status(thm)], ['0', '57'])).
% 17.12/17.32  
% 17.12/17.32  % SZS output end Refutation
% 17.12/17.32  
% 17.12/17.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
