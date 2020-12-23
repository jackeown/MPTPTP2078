%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zt7gpeHIxo

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:25 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  277 (1271 expanded)
%              Number of leaves         :   51 ( 396 expanded)
%              Depth                    :   25
%              Number of atoms          : 2749 (26502 expanded)
%              Number of equality atoms :  191 (1785 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
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

thf('9',plain,(
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

thf('10',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
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
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','20','21','22'])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('37',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('38',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
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

thf('41',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('48',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','50'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('52',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('53',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','55'])).

thf('57',plain,(
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

thf('58',plain,(
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

thf('59',plain,(
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
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('64',plain,(
    ! [X16: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('65',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['63','64','65','66','67','68'])).

thf('70',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('72',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v2_funct_1 @ X42 )
      | ~ ( zip_tseitin_0 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('76',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('81',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('82',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['80','81'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('83',plain,(
    ! [X5: $i] :
      ( ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('84',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('85',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('86',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ X13 )
        = ( k4_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('87',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('88',plain,(
    ! [X5: $i] :
      ( ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('90',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('91',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ X13 )
        = ( k4_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('92',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('93',plain,(
    ! [X5: $i] :
      ( ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('97',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['90','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('105',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ X12 @ ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('106',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('107',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ X7 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['105','111'])).

thf('113',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['104','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['84','118'])).

thf('120',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('121',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('122',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ X12 @ ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('123',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) )
      = ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['80','81'])).

thf('126',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['80','81'])).

thf('128',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( k4_relat_1 @ sk_D )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['119','126','127','128'])).

thf('130',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('131',plain,
    ( ( k4_relat_1 @ sk_D )
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['77','131'])).

thf('133',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ X13 )
        = ( k4_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('134',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X17 @ ( k2_funct_1 @ X17 ) ) )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['132','136'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('138',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('139',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['80','81'])).

thf('140',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('142',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['137','138','139','140','141'])).

thf('143',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('144',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('146',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X51 ) @ X51 )
        = ( k6_partfun1 @ X50 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('148',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('149',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X51 ) @ X51 )
        = ( k6_relat_1 @ X50 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('155',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X5: $i] :
      ( ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('159',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('161',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('163',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('164',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ X12 @ ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('165',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['162','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['155','156'])).

thf('168',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['155','156'])).

thf('170',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['161','168','169','170','171'])).

thf('173',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['150','151','152','172','173','174'])).

thf('176',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ X7 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['161','168','169','170','171'])).

thf('182',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('183',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['155','156'])).

thf('185',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['155','156'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['180','186','187'])).

thf('189',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['145','188'])).

thf('190',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('191',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['161','168','169','170','171'])).

thf('192',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X17 @ ( k2_funct_1 @ X17 ) ) )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('193',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('194',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['155','156'])).

thf('195',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['193','194','195','196'])).

thf('198',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
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

thf('200',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['161','168','169','170','171'])).

thf('204',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['200','201','202','203','204','205'])).

thf('207',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('211',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['197','209','210'])).

thf('212',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['190','211'])).

thf('213',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['80','81'])).

thf('214',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['189','212','213'])).

thf('215',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['80','81'])).

thf('216',plain,
    ( ( k4_relat_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['144','214','215'])).

thf('217',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ X13 )
        = ( k4_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('218',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( sk_D
     != ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['155','156'])).

thf('221',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['219','220','221','222'])).

thf('224',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['216','223'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zt7gpeHIxo
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:19 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.72/1.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.72/1.93  % Solved by: fo/fo7.sh
% 1.72/1.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.72/1.93  % done 1641 iterations in 1.471s
% 1.72/1.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.72/1.93  % SZS output start Refutation
% 1.72/1.93  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.72/1.93  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.72/1.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.72/1.93  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.72/1.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.72/1.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.72/1.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.72/1.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.72/1.93  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.72/1.93  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.72/1.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.72/1.93  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.72/1.93  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.72/1.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.72/1.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.72/1.93  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.72/1.93  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.72/1.93  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.72/1.93  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.72/1.93  thf(sk_C_type, type, sk_C: $i).
% 1.72/1.93  thf(sk_D_type, type, sk_D: $i).
% 1.72/1.93  thf(sk_B_type, type, sk_B: $i).
% 1.72/1.93  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.72/1.93  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.72/1.93  thf(sk_A_type, type, sk_A: $i).
% 1.72/1.93  thf(t36_funct_2, conjecture,
% 1.72/1.93    (![A:$i,B:$i,C:$i]:
% 1.72/1.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.72/1.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.93       ( ![D:$i]:
% 1.72/1.93         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.72/1.93             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.72/1.93           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.72/1.93               ( r2_relset_1 @
% 1.72/1.93                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.72/1.93                 ( k6_partfun1 @ A ) ) & 
% 1.72/1.93               ( v2_funct_1 @ C ) ) =>
% 1.72/1.93             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.72/1.93               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.72/1.93  thf(zf_stmt_0, negated_conjecture,
% 1.72/1.93    (~( ![A:$i,B:$i,C:$i]:
% 1.72/1.93        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.72/1.93            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.93          ( ![D:$i]:
% 1.72/1.93            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.72/1.93                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.72/1.93              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.72/1.93                  ( r2_relset_1 @
% 1.72/1.93                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.72/1.93                    ( k6_partfun1 @ A ) ) & 
% 1.72/1.93                  ( v2_funct_1 @ C ) ) =>
% 1.72/1.93                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.72/1.93                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.72/1.93    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.72/1.93  thf('0', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf(t35_funct_2, axiom,
% 1.72/1.93    (![A:$i,B:$i,C:$i]:
% 1.72/1.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.72/1.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.93       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.72/1.93         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.72/1.93           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.72/1.93             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.72/1.93  thf('1', plain,
% 1.72/1.93      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.72/1.93         (((X50) = (k1_xboole_0))
% 1.72/1.93          | ~ (v1_funct_1 @ X51)
% 1.72/1.93          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.72/1.93          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.72/1.93          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_partfun1 @ X52))
% 1.72/1.93          | ~ (v2_funct_1 @ X51)
% 1.72/1.93          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.72/1.93      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.72/1.93  thf(redefinition_k6_partfun1, axiom,
% 1.72/1.93    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.72/1.93  thf('2', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.72/1.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.72/1.93  thf('3', plain,
% 1.72/1.93      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.72/1.93         (((X50) = (k1_xboole_0))
% 1.72/1.93          | ~ (v1_funct_1 @ X51)
% 1.72/1.93          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.72/1.93          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.72/1.93          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_relat_1 @ X52))
% 1.72/1.93          | ~ (v2_funct_1 @ X51)
% 1.72/1.93          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.72/1.93      inference('demod', [status(thm)], ['1', '2'])).
% 1.72/1.93  thf('4', plain,
% 1.72/1.93      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.72/1.93        | ~ (v2_funct_1 @ sk_D)
% 1.72/1.93        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.72/1.93        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.72/1.93        | ~ (v1_funct_1 @ sk_D)
% 1.72/1.93        | ((sk_A) = (k1_xboole_0)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['0', '3'])).
% 1.72/1.93  thf('5', plain,
% 1.72/1.93      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.72/1.93        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.72/1.93        (k6_partfun1 @ sk_A))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('6', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.72/1.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.72/1.93  thf('7', plain,
% 1.72/1.93      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.72/1.93        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.72/1.93        (k6_relat_1 @ sk_A))),
% 1.72/1.93      inference('demod', [status(thm)], ['5', '6'])).
% 1.72/1.93  thf('8', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf(t24_funct_2, axiom,
% 1.72/1.93    (![A:$i,B:$i,C:$i]:
% 1.72/1.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.72/1.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.93       ( ![D:$i]:
% 1.72/1.93         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.72/1.93             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.72/1.93           ( ( r2_relset_1 @
% 1.72/1.93               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.72/1.93               ( k6_partfun1 @ B ) ) =>
% 1.72/1.93             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.72/1.93  thf('9', plain,
% 1.72/1.93      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.72/1.93         (~ (v1_funct_1 @ X37)
% 1.72/1.93          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 1.72/1.93          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.72/1.93          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 1.72/1.93               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 1.72/1.93               (k6_partfun1 @ X38))
% 1.72/1.93          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 1.72/1.93          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 1.72/1.93          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 1.72/1.93          | ~ (v1_funct_1 @ X40))),
% 1.72/1.93      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.72/1.93  thf('10', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.72/1.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.72/1.93  thf('11', plain,
% 1.72/1.93      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.72/1.93         (~ (v1_funct_1 @ X37)
% 1.72/1.93          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 1.72/1.93          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.72/1.93          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 1.72/1.93               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 1.72/1.93               (k6_relat_1 @ X38))
% 1.72/1.93          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 1.72/1.93          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 1.72/1.93          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 1.72/1.93          | ~ (v1_funct_1 @ X40))),
% 1.72/1.93      inference('demod', [status(thm)], ['9', '10'])).
% 1.72/1.93  thf('12', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.72/1.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.72/1.93          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.72/1.93          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.72/1.93               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.72/1.93               (k6_relat_1 @ sk_A))
% 1.72/1.93          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.72/1.93          | ~ (v1_funct_1 @ sk_C))),
% 1.72/1.93      inference('sup-', [status(thm)], ['8', '11'])).
% 1.72/1.93  thf('13', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('15', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.72/1.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.72/1.93          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.72/1.93          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.72/1.93               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.72/1.93               (k6_relat_1 @ sk_A)))),
% 1.72/1.93      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.72/1.93  thf('16', plain,
% 1.72/1.93      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.72/1.93        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.72/1.93        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.72/1.93        | ~ (v1_funct_1 @ sk_D))),
% 1.72/1.93      inference('sup-', [status(thm)], ['7', '15'])).
% 1.72/1.93  thf('17', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('18', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('20', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 1.72/1.93      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 1.72/1.93  thf('21', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('23', plain,
% 1.72/1.93      ((((sk_A) != (sk_A))
% 1.72/1.93        | ~ (v2_funct_1 @ sk_D)
% 1.72/1.93        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.72/1.93        | ((sk_A) = (k1_xboole_0)))),
% 1.72/1.93      inference('demod', [status(thm)], ['4', '20', '21', '22'])).
% 1.72/1.93  thf('24', plain,
% 1.72/1.93      ((((sk_A) = (k1_xboole_0))
% 1.72/1.93        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.72/1.93        | ~ (v2_funct_1 @ sk_D))),
% 1.72/1.93      inference('simplify', [status(thm)], ['23'])).
% 1.72/1.93  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('26', plain,
% 1.72/1.93      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.72/1.93        | ~ (v2_funct_1 @ sk_D))),
% 1.72/1.93      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 1.72/1.93  thf('27', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('28', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf(redefinition_k1_partfun1, axiom,
% 1.72/1.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.72/1.93     ( ( ( v1_funct_1 @ E ) & 
% 1.72/1.93         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.72/1.93         ( v1_funct_1 @ F ) & 
% 1.72/1.93         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.72/1.93       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.72/1.93  thf('29', plain,
% 1.72/1.93      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.72/1.93         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.72/1.93          | ~ (v1_funct_1 @ X30)
% 1.72/1.93          | ~ (v1_funct_1 @ X33)
% 1.72/1.93          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.72/1.93          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 1.72/1.93              = (k5_relat_1 @ X30 @ X33)))),
% 1.72/1.93      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.72/1.93  thf('30', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.93         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.72/1.93            = (k5_relat_1 @ sk_C @ X0))
% 1.72/1.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ sk_C))),
% 1.72/1.93      inference('sup-', [status(thm)], ['28', '29'])).
% 1.72/1.93  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('32', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.93         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.72/1.93            = (k5_relat_1 @ sk_C @ X0))
% 1.72/1.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.72/1.93          | ~ (v1_funct_1 @ X0))),
% 1.72/1.93      inference('demod', [status(thm)], ['30', '31'])).
% 1.72/1.93  thf('33', plain,
% 1.72/1.93      ((~ (v1_funct_1 @ sk_D)
% 1.72/1.93        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.72/1.93            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['27', '32'])).
% 1.72/1.93  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('35', plain,
% 1.72/1.93      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.72/1.93         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.72/1.93      inference('demod', [status(thm)], ['33', '34'])).
% 1.72/1.93  thf('36', plain,
% 1.72/1.93      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.72/1.93        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.72/1.93        (k6_relat_1 @ sk_A))),
% 1.72/1.93      inference('demod', [status(thm)], ['5', '6'])).
% 1.72/1.93  thf('37', plain,
% 1.72/1.93      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.72/1.93         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.72/1.93      inference('demod', [status(thm)], ['33', '34'])).
% 1.72/1.93  thf('38', plain,
% 1.72/1.93      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.72/1.93        (k6_relat_1 @ sk_A))),
% 1.72/1.93      inference('demod', [status(thm)], ['36', '37'])).
% 1.72/1.93  thf('39', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('40', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf(dt_k1_partfun1, axiom,
% 1.72/1.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.72/1.93     ( ( ( v1_funct_1 @ E ) & 
% 1.72/1.93         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.72/1.93         ( v1_funct_1 @ F ) & 
% 1.72/1.93         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.72/1.93       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.72/1.93         ( m1_subset_1 @
% 1.72/1.93           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.72/1.93           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.72/1.93  thf('41', plain,
% 1.72/1.93      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.72/1.93         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.72/1.93          | ~ (v1_funct_1 @ X22)
% 1.72/1.93          | ~ (v1_funct_1 @ X25)
% 1.72/1.93          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.72/1.93          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 1.72/1.93             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 1.72/1.93      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.72/1.93  thf('42', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.93         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.72/1.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.72/1.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.72/1.93          | ~ (v1_funct_1 @ X1)
% 1.72/1.93          | ~ (v1_funct_1 @ sk_C))),
% 1.72/1.93      inference('sup-', [status(thm)], ['40', '41'])).
% 1.72/1.93  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('44', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.93         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.72/1.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.72/1.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.72/1.93          | ~ (v1_funct_1 @ X1))),
% 1.72/1.93      inference('demod', [status(thm)], ['42', '43'])).
% 1.72/1.93  thf('45', plain,
% 1.72/1.93      ((~ (v1_funct_1 @ sk_D)
% 1.72/1.93        | (m1_subset_1 @ 
% 1.72/1.93           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.72/1.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.72/1.93      inference('sup-', [status(thm)], ['39', '44'])).
% 1.72/1.93  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('47', plain,
% 1.72/1.93      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.72/1.93         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.72/1.93      inference('demod', [status(thm)], ['33', '34'])).
% 1.72/1.93  thf('48', plain,
% 1.72/1.93      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.72/1.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.72/1.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.72/1.93  thf(redefinition_r2_relset_1, axiom,
% 1.72/1.93    (![A:$i,B:$i,C:$i,D:$i]:
% 1.72/1.93     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.72/1.93         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.93       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.72/1.93  thf('49', plain,
% 1.72/1.93      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.72/1.93         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.72/1.93          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.72/1.93          | ((X18) = (X21))
% 1.72/1.93          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 1.72/1.93      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.72/1.93  thf('50', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.72/1.93          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.72/1.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.72/1.93      inference('sup-', [status(thm)], ['48', '49'])).
% 1.72/1.93  thf('51', plain,
% 1.72/1.93      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.72/1.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.72/1.93        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['38', '50'])).
% 1.72/1.93  thf(dt_k6_partfun1, axiom,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( m1_subset_1 @
% 1.72/1.93         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.72/1.93       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.72/1.93  thf('52', plain,
% 1.72/1.93      (![X29 : $i]:
% 1.72/1.93         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 1.72/1.93          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 1.72/1.93      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.72/1.93  thf('53', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.72/1.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.72/1.93  thf('54', plain,
% 1.72/1.93      (![X29 : $i]:
% 1.72/1.93         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 1.72/1.93          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 1.72/1.93      inference('demod', [status(thm)], ['52', '53'])).
% 1.72/1.93  thf('55', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 1.72/1.93      inference('demod', [status(thm)], ['51', '54'])).
% 1.72/1.93  thf('56', plain,
% 1.72/1.93      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.72/1.93         = (k6_relat_1 @ sk_A))),
% 1.72/1.93      inference('demod', [status(thm)], ['35', '55'])).
% 1.72/1.93  thf('57', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf(t30_funct_2, axiom,
% 1.72/1.93    (![A:$i,B:$i,C:$i,D:$i]:
% 1.72/1.93     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.72/1.93         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.72/1.93       ( ![E:$i]:
% 1.72/1.93         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.72/1.93             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.72/1.93           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.72/1.93               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.72/1.93             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.72/1.93               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.72/1.93  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.72/1.93  thf(zf_stmt_2, axiom,
% 1.72/1.93    (![C:$i,B:$i]:
% 1.72/1.93     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.72/1.93       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.72/1.93  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.72/1.93  thf(zf_stmt_4, axiom,
% 1.72/1.93    (![E:$i,D:$i]:
% 1.72/1.93     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.72/1.93  thf(zf_stmt_5, axiom,
% 1.72/1.93    (![A:$i,B:$i,C:$i,D:$i]:
% 1.72/1.93     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.72/1.93         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.93       ( ![E:$i]:
% 1.72/1.93         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.72/1.93             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.72/1.93           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.72/1.93               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.72/1.93             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.72/1.93  thf('58', plain,
% 1.72/1.93      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.72/1.93         (~ (v1_funct_1 @ X45)
% 1.72/1.93          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 1.72/1.93          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 1.72/1.93          | (zip_tseitin_0 @ X45 @ X48)
% 1.72/1.93          | ~ (v2_funct_1 @ (k1_partfun1 @ X49 @ X46 @ X46 @ X47 @ X48 @ X45))
% 1.72/1.93          | (zip_tseitin_1 @ X47 @ X46)
% 1.72/1.93          | ((k2_relset_1 @ X49 @ X46 @ X48) != (X46))
% 1.72/1.93          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X46)))
% 1.72/1.93          | ~ (v1_funct_2 @ X48 @ X49 @ X46)
% 1.72/1.93          | ~ (v1_funct_1 @ X48))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.72/1.93  thf('59', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]:
% 1.72/1.93         (~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.72/1.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.72/1.93          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.72/1.93          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.72/1.93          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.72/1.93          | (zip_tseitin_0 @ sk_D @ X0)
% 1.72/1.93          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.72/1.93          | ~ (v1_funct_1 @ sk_D))),
% 1.72/1.93      inference('sup-', [status(thm)], ['57', '58'])).
% 1.72/1.93  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('62', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]:
% 1.72/1.93         (~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.72/1.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.72/1.93          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.72/1.93          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.72/1.93          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.72/1.93          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.72/1.93      inference('demod', [status(thm)], ['59', '60', '61'])).
% 1.72/1.93  thf('63', plain,
% 1.72/1.93      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.72/1.93        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.72/1.93        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.72/1.93        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.72/1.93        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.72/1.93        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.72/1.93        | ~ (v1_funct_1 @ sk_C))),
% 1.72/1.93      inference('sup-', [status(thm)], ['56', '62'])).
% 1.72/1.93  thf(fc4_funct_1, axiom,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.72/1.93       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.72/1.93  thf('64', plain, (![X16 : $i]: (v2_funct_1 @ (k6_relat_1 @ X16))),
% 1.72/1.93      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.72/1.93  thf('65', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('66', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('67', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('69', plain,
% 1.72/1.93      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.72/1.93        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.72/1.93        | ((sk_B) != (sk_B)))),
% 1.72/1.93      inference('demod', [status(thm)], ['63', '64', '65', '66', '67', '68'])).
% 1.72/1.93  thf('70', plain,
% 1.72/1.93      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.72/1.93      inference('simplify', [status(thm)], ['69'])).
% 1.72/1.93  thf('71', plain,
% 1.72/1.93      (![X43 : $i, X44 : $i]:
% 1.72/1.93         (((X43) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X43 @ X44))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.72/1.93  thf('72', plain,
% 1.72/1.93      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['70', '71'])).
% 1.72/1.93  thf('73', plain, (((sk_A) != (k1_xboole_0))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('74', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.72/1.93      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 1.72/1.93  thf('75', plain,
% 1.72/1.93      (![X41 : $i, X42 : $i]:
% 1.72/1.93         ((v2_funct_1 @ X42) | ~ (zip_tseitin_0 @ X42 @ X41))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.72/1.93  thf('76', plain, ((v2_funct_1 @ sk_D)),
% 1.72/1.93      inference('sup-', [status(thm)], ['74', '75'])).
% 1.72/1.93  thf('77', plain,
% 1.72/1.93      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 1.72/1.93      inference('demod', [status(thm)], ['26', '76'])).
% 1.72/1.93  thf('78', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf(cc2_relat_1, axiom,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( v1_relat_1 @ A ) =>
% 1.72/1.93       ( ![B:$i]:
% 1.72/1.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.72/1.93  thf('79', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]:
% 1.72/1.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.72/1.93          | (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X1))),
% 1.72/1.93      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.72/1.93  thf('80', plain,
% 1.72/1.93      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.72/1.93      inference('sup-', [status(thm)], ['78', '79'])).
% 1.72/1.93  thf(fc6_relat_1, axiom,
% 1.72/1.93    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.72/1.93  thf('81', plain,
% 1.72/1.93      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 1.72/1.93      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.72/1.93  thf('82', plain, ((v1_relat_1 @ sk_D)),
% 1.72/1.93      inference('demod', [status(thm)], ['80', '81'])).
% 1.72/1.93  thf(t37_relat_1, axiom,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( v1_relat_1 @ A ) =>
% 1.72/1.93       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 1.72/1.93         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 1.72/1.93  thf('83', plain,
% 1.72/1.93      (![X5 : $i]:
% 1.72/1.93         (((k1_relat_1 @ X5) = (k2_relat_1 @ (k4_relat_1 @ X5)))
% 1.72/1.93          | ~ (v1_relat_1 @ X5))),
% 1.72/1.93      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.72/1.93  thf('84', plain,
% 1.72/1.93      (((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['82', '83'])).
% 1.72/1.93  thf(dt_k4_relat_1, axiom,
% 1.72/1.93    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 1.72/1.93  thf('85', plain,
% 1.72/1.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 1.72/1.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.72/1.93  thf(d9_funct_1, axiom,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.72/1.93       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.72/1.93  thf('86', plain,
% 1.72/1.93      (![X13 : $i]:
% 1.72/1.93         (~ (v2_funct_1 @ X13)
% 1.72/1.93          | ((k2_funct_1 @ X13) = (k4_relat_1 @ X13))
% 1.72/1.93          | ~ (v1_funct_1 @ X13)
% 1.72/1.93          | ~ (v1_relat_1 @ X13))),
% 1.72/1.93      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.72/1.93  thf('87', plain,
% 1.72/1.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 1.72/1.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.72/1.93  thf('88', plain,
% 1.72/1.93      (![X5 : $i]:
% 1.72/1.93         (((k1_relat_1 @ X5) = (k2_relat_1 @ (k4_relat_1 @ X5)))
% 1.72/1.93          | ~ (v1_relat_1 @ X5))),
% 1.72/1.93      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.72/1.93  thf('89', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (~ (v1_relat_1 @ X0)
% 1.72/1.93          | ((k1_relat_1 @ (k4_relat_1 @ X0))
% 1.72/1.93              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 1.72/1.93      inference('sup-', [status(thm)], ['87', '88'])).
% 1.72/1.93  thf(dt_k2_funct_1, axiom,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.72/1.93       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.72/1.93         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.72/1.93  thf('90', plain,
% 1.72/1.93      (![X14 : $i]:
% 1.72/1.93         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 1.72/1.93          | ~ (v1_funct_1 @ X14)
% 1.72/1.93          | ~ (v1_relat_1 @ X14))),
% 1.72/1.93      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.72/1.93  thf('91', plain,
% 1.72/1.93      (![X13 : $i]:
% 1.72/1.93         (~ (v2_funct_1 @ X13)
% 1.72/1.93          | ((k2_funct_1 @ X13) = (k4_relat_1 @ X13))
% 1.72/1.93          | ~ (v1_funct_1 @ X13)
% 1.72/1.93          | ~ (v1_relat_1 @ X13))),
% 1.72/1.93      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.72/1.93  thf('92', plain,
% 1.72/1.93      (![X14 : $i]:
% 1.72/1.93         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 1.72/1.93          | ~ (v1_funct_1 @ X14)
% 1.72/1.93          | ~ (v1_relat_1 @ X14))),
% 1.72/1.93      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.72/1.93  thf('93', plain,
% 1.72/1.93      (![X5 : $i]:
% 1.72/1.93         (((k1_relat_1 @ X5) = (k2_relat_1 @ (k4_relat_1 @ X5)))
% 1.72/1.93          | ~ (v1_relat_1 @ X5))),
% 1.72/1.93      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.72/1.93  thf('94', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (~ (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 1.72/1.93              = (k2_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.72/1.93      inference('sup-', [status(thm)], ['92', '93'])).
% 1.72/1.93  thf('95', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (((k1_relat_1 @ (k2_funct_1 @ X0))
% 1.72/1.93            = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v2_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X0))),
% 1.72/1.93      inference('sup+', [status(thm)], ['91', '94'])).
% 1.72/1.93  thf('96', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (~ (v2_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 1.72/1.93              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 1.72/1.93      inference('simplify', [status(thm)], ['95'])).
% 1.72/1.93  thf(t78_relat_1, axiom,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( v1_relat_1 @ A ) =>
% 1.72/1.93       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.72/1.93  thf('97', plain,
% 1.72/1.93      (![X11 : $i]:
% 1.72/1.93         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 1.72/1.93          | ~ (v1_relat_1 @ X11))),
% 1.72/1.93      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.72/1.93  thf('98', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (((k5_relat_1 @ 
% 1.72/1.93            (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))) @ 
% 1.72/1.93            (k2_funct_1 @ X0)) = (k2_funct_1 @ X0))
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v2_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.72/1.93      inference('sup+', [status(thm)], ['96', '97'])).
% 1.72/1.93  thf('99', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (~ (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v2_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ((k5_relat_1 @ 
% 1.72/1.93              (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))) @ 
% 1.72/1.93              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['90', '98'])).
% 1.72/1.93  thf('100', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (((k5_relat_1 @ 
% 1.72/1.93            (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))) @ 
% 1.72/1.93            (k2_funct_1 @ X0)) = (k2_funct_1 @ X0))
% 1.72/1.93          | ~ (v2_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X0))),
% 1.72/1.93      inference('simplify', [status(thm)], ['99'])).
% 1.72/1.93  thf('101', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))) @ 
% 1.72/1.93            (k2_funct_1 @ X0)) = (k2_funct_1 @ X0))
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v2_funct_1 @ X0))),
% 1.72/1.93      inference('sup+', [status(thm)], ['89', '100'])).
% 1.72/1.93  thf('102', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (~ (v2_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))) @ 
% 1.72/1.93              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 1.72/1.93      inference('simplify', [status(thm)], ['101'])).
% 1.72/1.93  thf('103', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))) @ 
% 1.72/1.93            (k4_relat_1 @ X0)) = (k2_funct_1 @ X0))
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v2_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v2_funct_1 @ X0))),
% 1.72/1.93      inference('sup+', [status(thm)], ['86', '102'])).
% 1.72/1.93  thf('104', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (~ (v2_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))) @ 
% 1.72/1.93              (k4_relat_1 @ X0)) = (k2_funct_1 @ X0)))),
% 1.72/1.93      inference('simplify', [status(thm)], ['103'])).
% 1.72/1.93  thf(t80_relat_1, axiom,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( v1_relat_1 @ A ) =>
% 1.72/1.93       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.72/1.93  thf('105', plain,
% 1.72/1.93      (![X12 : $i]:
% 1.72/1.93         (((k5_relat_1 @ X12 @ (k6_relat_1 @ (k2_relat_1 @ X12))) = (X12))
% 1.72/1.93          | ~ (v1_relat_1 @ X12))),
% 1.72/1.93      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.72/1.93  thf('106', plain,
% 1.72/1.93      (![X11 : $i]:
% 1.72/1.93         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 1.72/1.93          | ~ (v1_relat_1 @ X11))),
% 1.72/1.93      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.72/1.93  thf(t55_relat_1, axiom,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( v1_relat_1 @ A ) =>
% 1.72/1.93       ( ![B:$i]:
% 1.72/1.93         ( ( v1_relat_1 @ B ) =>
% 1.72/1.93           ( ![C:$i]:
% 1.72/1.93             ( ( v1_relat_1 @ C ) =>
% 1.72/1.93               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.72/1.93                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.72/1.93  thf('107', plain,
% 1.72/1.93      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.72/1.93         (~ (v1_relat_1 @ X6)
% 1.72/1.93          | ((k5_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 1.72/1.93              = (k5_relat_1 @ X7 @ (k5_relat_1 @ X6 @ X8)))
% 1.72/1.93          | ~ (v1_relat_1 @ X8)
% 1.72/1.93          | ~ (v1_relat_1 @ X7))),
% 1.72/1.93      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.72/1.93  thf('108', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]:
% 1.72/1.93         (((k5_relat_1 @ X0 @ X1)
% 1.72/1.93            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.72/1.93               (k5_relat_1 @ X0 @ X1)))
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.72/1.93          | ~ (v1_relat_1 @ X1)
% 1.72/1.93          | ~ (v1_relat_1 @ X0))),
% 1.72/1.93      inference('sup+', [status(thm)], ['106', '107'])).
% 1.72/1.93  thf('109', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 1.72/1.93      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.72/1.93  thf('110', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]:
% 1.72/1.93         (((k5_relat_1 @ X0 @ X1)
% 1.72/1.93            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.72/1.93               (k5_relat_1 @ X0 @ X1)))
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X1)
% 1.72/1.93          | ~ (v1_relat_1 @ X0))),
% 1.72/1.93      inference('demod', [status(thm)], ['108', '109'])).
% 1.72/1.93  thf('111', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]:
% 1.72/1.93         (~ (v1_relat_1 @ X1)
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ((k5_relat_1 @ X0 @ X1)
% 1.72/1.93              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.72/1.93                 (k5_relat_1 @ X0 @ X1))))),
% 1.72/1.93      inference('simplify', [status(thm)], ['110'])).
% 1.72/1.93  thf('112', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 1.72/1.93            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 1.72/1.93      inference('sup+', [status(thm)], ['105', '111'])).
% 1.72/1.93  thf('113', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 1.72/1.93      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.72/1.93  thf('114', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 1.72/1.93            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X0))),
% 1.72/1.93      inference('demod', [status(thm)], ['112', '113'])).
% 1.72/1.93  thf('115', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (~ (v1_relat_1 @ X0)
% 1.72/1.93          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 1.72/1.93              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0)))),
% 1.72/1.93      inference('simplify', [status(thm)], ['114'])).
% 1.72/1.93  thf('116', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (((k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 1.72/1.93            (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 1.72/1.93            = (k2_funct_1 @ X0))
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v2_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 1.72/1.93      inference('sup+', [status(thm)], ['104', '115'])).
% 1.72/1.93  thf('117', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (~ (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v2_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ((k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 1.72/1.93              (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 1.72/1.93              = (k2_funct_1 @ X0)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['85', '116'])).
% 1.72/1.93  thf('118', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (((k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 1.72/1.93            (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 1.72/1.93            = (k2_funct_1 @ X0))
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v2_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X0))),
% 1.72/1.93      inference('simplify', [status(thm)], ['117'])).
% 1.72/1.93  thf('119', plain,
% 1.72/1.93      ((((k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_relat_1 @ (k1_relat_1 @ sk_D)))
% 1.72/1.93          = (k2_funct_1 @ sk_D))
% 1.72/1.93        | ~ (v1_relat_1 @ sk_D)
% 1.72/1.93        | ~ (v2_funct_1 @ sk_D)
% 1.72/1.93        | ~ (v1_funct_1 @ sk_D))),
% 1.72/1.93      inference('sup+', [status(thm)], ['84', '118'])).
% 1.72/1.93  thf('120', plain,
% 1.72/1.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 1.72/1.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.72/1.93  thf('121', plain,
% 1.72/1.93      (((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['82', '83'])).
% 1.72/1.93  thf('122', plain,
% 1.72/1.93      (![X12 : $i]:
% 1.72/1.93         (((k5_relat_1 @ X12 @ (k6_relat_1 @ (k2_relat_1 @ X12))) = (X12))
% 1.72/1.93          | ~ (v1_relat_1 @ X12))),
% 1.72/1.93      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.72/1.93  thf('123', plain,
% 1.72/1.93      ((((k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_relat_1 @ (k1_relat_1 @ sk_D)))
% 1.72/1.93          = (k4_relat_1 @ sk_D))
% 1.72/1.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 1.72/1.93      inference('sup+', [status(thm)], ['121', '122'])).
% 1.72/1.93  thf('124', plain,
% 1.72/1.93      ((~ (v1_relat_1 @ sk_D)
% 1.72/1.93        | ((k5_relat_1 @ (k4_relat_1 @ sk_D) @ 
% 1.72/1.93            (k6_relat_1 @ (k1_relat_1 @ sk_D))) = (k4_relat_1 @ sk_D)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['120', '123'])).
% 1.72/1.93  thf('125', plain, ((v1_relat_1 @ sk_D)),
% 1.72/1.93      inference('demod', [status(thm)], ['80', '81'])).
% 1.72/1.93  thf('126', plain,
% 1.72/1.93      (((k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_relat_1 @ (k1_relat_1 @ sk_D)))
% 1.72/1.93         = (k4_relat_1 @ sk_D))),
% 1.72/1.93      inference('demod', [status(thm)], ['124', '125'])).
% 1.72/1.93  thf('127', plain, ((v1_relat_1 @ sk_D)),
% 1.72/1.93      inference('demod', [status(thm)], ['80', '81'])).
% 1.72/1.93  thf('128', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('129', plain,
% 1.72/1.93      ((((k4_relat_1 @ sk_D) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 1.72/1.93      inference('demod', [status(thm)], ['119', '126', '127', '128'])).
% 1.72/1.93  thf('130', plain, ((v2_funct_1 @ sk_D)),
% 1.72/1.93      inference('sup-', [status(thm)], ['74', '75'])).
% 1.72/1.93  thf('131', plain, (((k4_relat_1 @ sk_D) = (k2_funct_1 @ sk_D))),
% 1.72/1.93      inference('demod', [status(thm)], ['129', '130'])).
% 1.72/1.93  thf('132', plain,
% 1.72/1.93      (((k5_relat_1 @ sk_D @ (k4_relat_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 1.72/1.93      inference('demod', [status(thm)], ['77', '131'])).
% 1.72/1.93  thf('133', plain,
% 1.72/1.93      (![X13 : $i]:
% 1.72/1.93         (~ (v2_funct_1 @ X13)
% 1.72/1.93          | ((k2_funct_1 @ X13) = (k4_relat_1 @ X13))
% 1.72/1.93          | ~ (v1_funct_1 @ X13)
% 1.72/1.93          | ~ (v1_relat_1 @ X13))),
% 1.72/1.93      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.72/1.93  thf(t58_funct_1, axiom,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.72/1.93       ( ( v2_funct_1 @ A ) =>
% 1.72/1.93         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.72/1.93             ( k1_relat_1 @ A ) ) & 
% 1.72/1.93           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.72/1.93             ( k1_relat_1 @ A ) ) ) ) ))).
% 1.72/1.93  thf('134', plain,
% 1.72/1.93      (![X17 : $i]:
% 1.72/1.93         (~ (v2_funct_1 @ X17)
% 1.72/1.93          | ((k2_relat_1 @ (k5_relat_1 @ X17 @ (k2_funct_1 @ X17)))
% 1.72/1.93              = (k1_relat_1 @ X17))
% 1.72/1.93          | ~ (v1_funct_1 @ X17)
% 1.72/1.93          | ~ (v1_relat_1 @ X17))),
% 1.72/1.93      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.72/1.93  thf('135', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 1.72/1.93            = (k1_relat_1 @ X0))
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v2_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v2_funct_1 @ X0))),
% 1.72/1.93      inference('sup+', [status(thm)], ['133', '134'])).
% 1.72/1.93  thf('136', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (~ (v2_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X0)
% 1.72/1.93          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 1.72/1.93              = (k1_relat_1 @ X0)))),
% 1.72/1.93      inference('simplify', [status(thm)], ['135'])).
% 1.72/1.93  thf('137', plain,
% 1.72/1.93      ((((k2_relat_1 @ (k6_relat_1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 1.72/1.93        | ~ (v1_relat_1 @ sk_D)
% 1.72/1.93        | ~ (v1_funct_1 @ sk_D)
% 1.72/1.93        | ~ (v2_funct_1 @ sk_D))),
% 1.72/1.93      inference('sup+', [status(thm)], ['132', '136'])).
% 1.72/1.93  thf(t71_relat_1, axiom,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.72/1.93       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.72/1.93  thf('138', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 1.72/1.93      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.72/1.93  thf('139', plain, ((v1_relat_1 @ sk_D)),
% 1.72/1.93      inference('demod', [status(thm)], ['80', '81'])).
% 1.72/1.93  thf('140', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('141', plain, ((v2_funct_1 @ sk_D)),
% 1.72/1.93      inference('sup-', [status(thm)], ['74', '75'])).
% 1.72/1.93  thf('142', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.72/1.93      inference('demod', [status(thm)], ['137', '138', '139', '140', '141'])).
% 1.72/1.93  thf('143', plain,
% 1.72/1.93      (![X11 : $i]:
% 1.72/1.93         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 1.72/1.93          | ~ (v1_relat_1 @ X11))),
% 1.72/1.93      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.72/1.93  thf('144', plain,
% 1.72/1.93      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (sk_D))
% 1.72/1.93        | ~ (v1_relat_1 @ sk_D))),
% 1.72/1.93      inference('sup+', [status(thm)], ['142', '143'])).
% 1.72/1.93  thf('145', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 1.72/1.93      inference('demod', [status(thm)], ['51', '54'])).
% 1.72/1.93  thf('146', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('147', plain,
% 1.72/1.93      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.72/1.93         (((X50) = (k1_xboole_0))
% 1.72/1.93          | ~ (v1_funct_1 @ X51)
% 1.72/1.93          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.72/1.93          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.72/1.93          | ((k5_relat_1 @ (k2_funct_1 @ X51) @ X51) = (k6_partfun1 @ X50))
% 1.72/1.93          | ~ (v2_funct_1 @ X51)
% 1.72/1.93          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.72/1.93      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.72/1.93  thf('148', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.72/1.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.72/1.93  thf('149', plain,
% 1.72/1.93      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.72/1.93         (((X50) = (k1_xboole_0))
% 1.72/1.93          | ~ (v1_funct_1 @ X51)
% 1.72/1.93          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.72/1.93          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.72/1.93          | ((k5_relat_1 @ (k2_funct_1 @ X51) @ X51) = (k6_relat_1 @ X50))
% 1.72/1.93          | ~ (v2_funct_1 @ X51)
% 1.72/1.93          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.72/1.93      inference('demod', [status(thm)], ['147', '148'])).
% 1.72/1.93  thf('150', plain,
% 1.72/1.93      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.72/1.93        | ~ (v2_funct_1 @ sk_C)
% 1.72/1.93        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 1.72/1.93        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.72/1.93        | ~ (v1_funct_1 @ sk_C)
% 1.72/1.93        | ((sk_B) = (k1_xboole_0)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['146', '149'])).
% 1.72/1.93  thf('151', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('152', plain, ((v2_funct_1 @ sk_C)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('153', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('154', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]:
% 1.72/1.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.72/1.93          | (v1_relat_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X1))),
% 1.72/1.93      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.72/1.93  thf('155', plain,
% 1.72/1.93      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.72/1.93      inference('sup-', [status(thm)], ['153', '154'])).
% 1.72/1.93  thf('156', plain,
% 1.72/1.93      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 1.72/1.93      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.72/1.93  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.93      inference('demod', [status(thm)], ['155', '156'])).
% 1.72/1.93  thf('158', plain,
% 1.72/1.93      (![X5 : $i]:
% 1.72/1.93         (((k1_relat_1 @ X5) = (k2_relat_1 @ (k4_relat_1 @ X5)))
% 1.72/1.93          | ~ (v1_relat_1 @ X5))),
% 1.72/1.93      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.72/1.93  thf('159', plain,
% 1.72/1.93      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['157', '158'])).
% 1.72/1.93  thf('160', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (((k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 1.72/1.93            (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 1.72/1.93            = (k2_funct_1 @ X0))
% 1.72/1.93          | ~ (v1_funct_1 @ X0)
% 1.72/1.93          | ~ (v2_funct_1 @ X0)
% 1.72/1.93          | ~ (v1_relat_1 @ X0))),
% 1.72/1.93      inference('simplify', [status(thm)], ['117'])).
% 1.72/1.93  thf('161', plain,
% 1.72/1.93      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 1.72/1.93          = (k2_funct_1 @ sk_C))
% 1.72/1.93        | ~ (v1_relat_1 @ sk_C)
% 1.72/1.93        | ~ (v2_funct_1 @ sk_C)
% 1.72/1.93        | ~ (v1_funct_1 @ sk_C))),
% 1.72/1.93      inference('sup+', [status(thm)], ['159', '160'])).
% 1.72/1.93  thf('162', plain,
% 1.72/1.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 1.72/1.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.72/1.93  thf('163', plain,
% 1.72/1.93      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['157', '158'])).
% 1.72/1.93  thf('164', plain,
% 1.72/1.93      (![X12 : $i]:
% 1.72/1.93         (((k5_relat_1 @ X12 @ (k6_relat_1 @ (k2_relat_1 @ X12))) = (X12))
% 1.72/1.93          | ~ (v1_relat_1 @ X12))),
% 1.72/1.93      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.72/1.93  thf('165', plain,
% 1.72/1.93      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 1.72/1.93          = (k4_relat_1 @ sk_C))
% 1.72/1.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.72/1.93      inference('sup+', [status(thm)], ['163', '164'])).
% 1.72/1.93  thf('166', plain,
% 1.72/1.93      ((~ (v1_relat_1 @ sk_C)
% 1.72/1.93        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 1.72/1.93            (k6_relat_1 @ (k1_relat_1 @ sk_C))) = (k4_relat_1 @ sk_C)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['162', '165'])).
% 1.72/1.93  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.93      inference('demod', [status(thm)], ['155', '156'])).
% 1.72/1.93  thf('168', plain,
% 1.72/1.93      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 1.72/1.93         = (k4_relat_1 @ sk_C))),
% 1.72/1.93      inference('demod', [status(thm)], ['166', '167'])).
% 1.72/1.93  thf('169', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.93      inference('demod', [status(thm)], ['155', '156'])).
% 1.72/1.93  thf('170', plain, ((v2_funct_1 @ sk_C)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('172', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 1.72/1.93      inference('demod', [status(thm)], ['161', '168', '169', '170', '171'])).
% 1.72/1.93  thf('173', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('175', plain,
% 1.72/1.93      ((((sk_B) != (sk_B))
% 1.72/1.93        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 1.72/1.93        | ((sk_B) = (k1_xboole_0)))),
% 1.72/1.93      inference('demod', [status(thm)],
% 1.72/1.93                ['150', '151', '152', '172', '173', '174'])).
% 1.72/1.93  thf('176', plain,
% 1.72/1.93      ((((sk_B) = (k1_xboole_0))
% 1.72/1.93        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 1.72/1.93      inference('simplify', [status(thm)], ['175'])).
% 1.72/1.93  thf('177', plain, (((sk_B) != (k1_xboole_0))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('178', plain,
% 1.72/1.93      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 1.72/1.93      inference('simplify_reflect-', [status(thm)], ['176', '177'])).
% 1.72/1.93  thf('179', plain,
% 1.72/1.93      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.72/1.93         (~ (v1_relat_1 @ X6)
% 1.72/1.93          | ((k5_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 1.72/1.93              = (k5_relat_1 @ X7 @ (k5_relat_1 @ X6 @ X8)))
% 1.72/1.93          | ~ (v1_relat_1 @ X8)
% 1.72/1.93          | ~ (v1_relat_1 @ X7))),
% 1.72/1.93      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.72/1.94  thf('180', plain,
% 1.72/1.94      (![X0 : $i]:
% 1.72/1.94         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 1.72/1.94            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.72/1.94          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.72/1.94          | ~ (v1_relat_1 @ X0)
% 1.72/1.94          | ~ (v1_relat_1 @ sk_C))),
% 1.72/1.94      inference('sup+', [status(thm)], ['178', '179'])).
% 1.72/1.94  thf('181', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 1.72/1.94      inference('demod', [status(thm)], ['161', '168', '169', '170', '171'])).
% 1.72/1.94  thf('182', plain,
% 1.72/1.94      (![X14 : $i]:
% 1.72/1.94         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 1.72/1.94          | ~ (v1_funct_1 @ X14)
% 1.72/1.94          | ~ (v1_relat_1 @ X14))),
% 1.72/1.94      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.72/1.94  thf('183', plain,
% 1.72/1.94      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.72/1.94        | ~ (v1_relat_1 @ sk_C)
% 1.72/1.94        | ~ (v1_funct_1 @ sk_C))),
% 1.72/1.94      inference('sup+', [status(thm)], ['181', '182'])).
% 1.72/1.94  thf('184', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.94      inference('demod', [status(thm)], ['155', '156'])).
% 1.72/1.94  thf('185', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.94  thf('186', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 1.72/1.94      inference('demod', [status(thm)], ['183', '184', '185'])).
% 1.72/1.94  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.94      inference('demod', [status(thm)], ['155', '156'])).
% 1.72/1.94  thf('188', plain,
% 1.72/1.94      (![X0 : $i]:
% 1.72/1.94         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 1.72/1.94            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.72/1.94          | ~ (v1_relat_1 @ X0))),
% 1.72/1.94      inference('demod', [status(thm)], ['180', '186', '187'])).
% 1.72/1.94  thf('189', plain,
% 1.72/1.94      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D)
% 1.72/1.94          = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 1.72/1.94        | ~ (v1_relat_1 @ sk_D))),
% 1.72/1.94      inference('sup+', [status(thm)], ['145', '188'])).
% 1.72/1.94  thf('190', plain,
% 1.72/1.94      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 1.72/1.94         = (k4_relat_1 @ sk_C))),
% 1.72/1.94      inference('demod', [status(thm)], ['166', '167'])).
% 1.72/1.94  thf('191', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 1.72/1.94      inference('demod', [status(thm)], ['161', '168', '169', '170', '171'])).
% 1.72/1.94  thf('192', plain,
% 1.72/1.94      (![X17 : $i]:
% 1.72/1.94         (~ (v2_funct_1 @ X17)
% 1.72/1.94          | ((k2_relat_1 @ (k5_relat_1 @ X17 @ (k2_funct_1 @ X17)))
% 1.72/1.94              = (k1_relat_1 @ X17))
% 1.72/1.94          | ~ (v1_funct_1 @ X17)
% 1.72/1.94          | ~ (v1_relat_1 @ X17))),
% 1.72/1.94      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.72/1.94  thf('193', plain,
% 1.72/1.94      ((((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)))
% 1.72/1.94          = (k1_relat_1 @ sk_C))
% 1.72/1.94        | ~ (v1_relat_1 @ sk_C)
% 1.72/1.94        | ~ (v1_funct_1 @ sk_C)
% 1.72/1.94        | ~ (v2_funct_1 @ sk_C))),
% 1.72/1.94      inference('sup+', [status(thm)], ['191', '192'])).
% 1.72/1.94  thf('194', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.94      inference('demod', [status(thm)], ['155', '156'])).
% 1.72/1.94  thf('195', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.94  thf('196', plain, ((v2_funct_1 @ sk_C)),
% 1.72/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.94  thf('197', plain,
% 1.72/1.94      (((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)))
% 1.72/1.94         = (k1_relat_1 @ sk_C))),
% 1.72/1.94      inference('demod', [status(thm)], ['193', '194', '195', '196'])).
% 1.72/1.94  thf('198', plain,
% 1.72/1.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.94  thf('199', plain,
% 1.72/1.94      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.72/1.94         (((X50) = (k1_xboole_0))
% 1.72/1.94          | ~ (v1_funct_1 @ X51)
% 1.72/1.94          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.72/1.94          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.72/1.94          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_relat_1 @ X52))
% 1.72/1.94          | ~ (v2_funct_1 @ X51)
% 1.72/1.94          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.72/1.94      inference('demod', [status(thm)], ['1', '2'])).
% 1.72/1.94  thf('200', plain,
% 1.72/1.94      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.72/1.94        | ~ (v2_funct_1 @ sk_C)
% 1.72/1.94        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.72/1.94        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.72/1.94        | ~ (v1_funct_1 @ sk_C)
% 1.72/1.94        | ((sk_B) = (k1_xboole_0)))),
% 1.72/1.94      inference('sup-', [status(thm)], ['198', '199'])).
% 1.72/1.94  thf('201', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.72/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.94  thf('202', plain, ((v2_funct_1 @ sk_C)),
% 1.72/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.94  thf('203', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 1.72/1.94      inference('demod', [status(thm)], ['161', '168', '169', '170', '171'])).
% 1.72/1.94  thf('204', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.72/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.94  thf('205', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.94  thf('206', plain,
% 1.72/1.94      ((((sk_B) != (sk_B))
% 1.72/1.94        | ((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.72/1.94        | ((sk_B) = (k1_xboole_0)))),
% 1.72/1.94      inference('demod', [status(thm)],
% 1.72/1.94                ['200', '201', '202', '203', '204', '205'])).
% 1.72/1.94  thf('207', plain,
% 1.72/1.94      ((((sk_B) = (k1_xboole_0))
% 1.72/1.94        | ((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 1.72/1.94      inference('simplify', [status(thm)], ['206'])).
% 1.72/1.94  thf('208', plain, (((sk_B) != (k1_xboole_0))),
% 1.72/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.94  thf('209', plain,
% 1.72/1.94      (((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 1.72/1.94      inference('simplify_reflect-', [status(thm)], ['207', '208'])).
% 1.72/1.94  thf('210', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 1.72/1.94      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.72/1.94  thf('211', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.72/1.94      inference('demod', [status(thm)], ['197', '209', '210'])).
% 1.72/1.94  thf('212', plain,
% 1.72/1.94      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ sk_A))
% 1.72/1.94         = (k4_relat_1 @ sk_C))),
% 1.72/1.94      inference('demod', [status(thm)], ['190', '211'])).
% 1.72/1.94  thf('213', plain, ((v1_relat_1 @ sk_D)),
% 1.72/1.94      inference('demod', [status(thm)], ['80', '81'])).
% 1.72/1.94  thf('214', plain,
% 1.72/1.94      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (k4_relat_1 @ sk_C))),
% 1.72/1.94      inference('demod', [status(thm)], ['189', '212', '213'])).
% 1.72/1.94  thf('215', plain, ((v1_relat_1 @ sk_D)),
% 1.72/1.94      inference('demod', [status(thm)], ['80', '81'])).
% 1.72/1.94  thf('216', plain, (((k4_relat_1 @ sk_C) = (sk_D))),
% 1.72/1.94      inference('demod', [status(thm)], ['144', '214', '215'])).
% 1.72/1.94  thf('217', plain,
% 1.72/1.94      (![X13 : $i]:
% 1.72/1.94         (~ (v2_funct_1 @ X13)
% 1.72/1.94          | ((k2_funct_1 @ X13) = (k4_relat_1 @ X13))
% 1.72/1.94          | ~ (v1_funct_1 @ X13)
% 1.72/1.94          | ~ (v1_relat_1 @ X13))),
% 1.72/1.94      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.72/1.94  thf('218', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.72/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.94  thf('219', plain,
% 1.72/1.94      ((((sk_D) != (k4_relat_1 @ sk_C))
% 1.72/1.94        | ~ (v1_relat_1 @ sk_C)
% 1.72/1.94        | ~ (v1_funct_1 @ sk_C)
% 1.72/1.94        | ~ (v2_funct_1 @ sk_C))),
% 1.72/1.94      inference('sup-', [status(thm)], ['217', '218'])).
% 1.72/1.94  thf('220', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.94      inference('demod', [status(thm)], ['155', '156'])).
% 1.72/1.94  thf('221', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.94  thf('222', plain, ((v2_funct_1 @ sk_C)),
% 1.72/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.94  thf('223', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 1.72/1.94      inference('demod', [status(thm)], ['219', '220', '221', '222'])).
% 1.72/1.94  thf('224', plain, ($false),
% 1.72/1.94      inference('simplify_reflect-', [status(thm)], ['216', '223'])).
% 1.72/1.94  
% 1.72/1.94  % SZS output end Refutation
% 1.72/1.94  
% 1.72/1.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
