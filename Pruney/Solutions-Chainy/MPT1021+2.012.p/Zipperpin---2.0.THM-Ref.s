%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MwKToggQRT

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:12 EST 2020

% Result     : Theorem 17.02s
% Output     : Refutation 17.02s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 533 expanded)
%              Number of leaves         :   46 ( 180 expanded)
%              Depth                    :   15
%              Number of atoms          : 1660 (11348 expanded)
%              Number of equality atoms :   56 ( 122 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(t88_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
        & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
          & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_funct_2])).

thf('0',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k2_funct_2 @ X50 @ X49 )
        = ( k2_funct_1 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X50 ) ) )
      | ~ ( v3_funct_2 @ X49 @ X50 @ X50 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X50 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X39: $i,X40: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( v3_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('20',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('21',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( v3_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('31',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','31'])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('37',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('39',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('43',plain,(
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

thf('44',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_2 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('45',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['45','46','47'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('49',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v2_funct_2 @ X38 @ X37 )
      | ( ( k2_relat_1 @ X38 )
        = X37 )
      | ~ ( v5_relat_1 @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('52',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('55',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('56',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['50','53','56'])).

thf('58',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('59',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('60',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('61',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['50','53','56'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('67',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf('73',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','70','71','72'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('74',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['74'])).

thf('76',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['50','53','56'])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf('80',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('82',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['41','82'])).

thf('84',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('85',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','85'])).

thf('87',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('88',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('95',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ X12 @ ( k2_funct_1 @ X12 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('97',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
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

thf('98',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('99',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('101',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('102',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('104',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('105',plain,(
    ! [X29: $i] :
      ( zip_tseitin_0 @ X29 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['103','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['106'])).

thf('108',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['102','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('110',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('111',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['99','108','111'])).

thf('113',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ X12 @ ( k2_funct_1 @ X12 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('114',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['112','115'])).

thf('117',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['99','108','111'])).

thf('118',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('119',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf('121',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['74'])).

thf('123',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['96','123'])).

thf('125',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['99','108','111'])).

thf('126',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf('127',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('129',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['124','125','126','127','128'])).

thf('130',plain,(
    $false ),
    inference(demod,[status(thm)],['86','95','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MwKToggQRT
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 17.02/17.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 17.02/17.19  % Solved by: fo/fo7.sh
% 17.02/17.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.02/17.19  % done 7050 iterations in 16.736s
% 17.02/17.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 17.02/17.19  % SZS output start Refutation
% 17.02/17.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 17.02/17.19  thf(sk_B_type, type, sk_B: $i).
% 17.02/17.19  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 17.02/17.19  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 17.02/17.19  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 17.02/17.19  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 17.02/17.19  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 17.02/17.19  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 17.02/17.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 17.02/17.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 17.02/17.19  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 17.02/17.19  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 17.02/17.19  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 17.02/17.19  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 17.02/17.19  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 17.02/17.19  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 17.02/17.19  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 17.02/17.19  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 17.02/17.19  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 17.02/17.19  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 17.02/17.19  thf(sk_A_type, type, sk_A: $i).
% 17.02/17.19  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 17.02/17.19  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 17.02/17.19  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 17.02/17.19  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 17.02/17.19  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 17.02/17.19  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 17.02/17.19  thf(t88_funct_2, conjecture,
% 17.02/17.19    (![A:$i,B:$i]:
% 17.02/17.19     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 17.02/17.19         ( v3_funct_2 @ B @ A @ A ) & 
% 17.02/17.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 17.02/17.19       ( ( r2_relset_1 @
% 17.02/17.19           A @ A @ 
% 17.02/17.19           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 17.02/17.19           ( k6_partfun1 @ A ) ) & 
% 17.02/17.19         ( r2_relset_1 @
% 17.02/17.19           A @ A @ 
% 17.02/17.19           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 17.02/17.19           ( k6_partfun1 @ A ) ) ) ))).
% 17.02/17.19  thf(zf_stmt_0, negated_conjecture,
% 17.02/17.19    (~( ![A:$i,B:$i]:
% 17.02/17.19        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 17.02/17.19            ( v3_funct_2 @ B @ A @ A ) & 
% 17.02/17.19            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 17.02/17.19          ( ( r2_relset_1 @
% 17.02/17.19              A @ A @ 
% 17.02/17.19              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 17.02/17.19              ( k6_partfun1 @ A ) ) & 
% 17.02/17.19            ( r2_relset_1 @
% 17.02/17.19              A @ A @ 
% 17.02/17.19              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 17.02/17.19              ( k6_partfun1 @ A ) ) ) ) )),
% 17.02/17.19    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 17.02/17.19  thf('0', plain,
% 17.02/17.19      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 17.02/17.19            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 17.02/17.19           (k6_partfun1 @ sk_A))
% 17.02/17.19        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 17.02/17.19              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 17.02/17.19             (k6_partfun1 @ sk_A)))),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('1', plain,
% 17.02/17.19      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 17.02/17.19            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 17.02/17.19           (k6_partfun1 @ sk_A)))
% 17.02/17.19         <= (~
% 17.02/17.19             ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 17.02/17.19                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 17.02/17.19               (k6_partfun1 @ sk_A))))),
% 17.02/17.19      inference('split', [status(esa)], ['0'])).
% 17.02/17.19  thf(redefinition_k6_partfun1, axiom,
% 17.02/17.19    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 17.02/17.19  thf('2', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 17.02/17.19      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 17.02/17.19  thf('3', plain,
% 17.02/17.19      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 17.02/17.19            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 17.02/17.19           (k6_relat_1 @ sk_A)))
% 17.02/17.19         <= (~
% 17.02/17.19             ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 17.02/17.19                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 17.02/17.19               (k6_partfun1 @ sk_A))))),
% 17.02/17.19      inference('demod', [status(thm)], ['1', '2'])).
% 17.02/17.19  thf('4', plain,
% 17.02/17.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf(redefinition_k2_funct_2, axiom,
% 17.02/17.19    (![A:$i,B:$i]:
% 17.02/17.19     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 17.02/17.19         ( v3_funct_2 @ B @ A @ A ) & 
% 17.02/17.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 17.02/17.19       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 17.02/17.19  thf('5', plain,
% 17.02/17.19      (![X49 : $i, X50 : $i]:
% 17.02/17.19         (((k2_funct_2 @ X50 @ X49) = (k2_funct_1 @ X49))
% 17.02/17.19          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X50)))
% 17.02/17.19          | ~ (v3_funct_2 @ X49 @ X50 @ X50)
% 17.02/17.19          | ~ (v1_funct_2 @ X49 @ X50 @ X50)
% 17.02/17.19          | ~ (v1_funct_1 @ X49))),
% 17.02/17.19      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 17.02/17.19  thf('6', plain,
% 17.02/17.19      ((~ (v1_funct_1 @ sk_B)
% 17.02/17.19        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 17.02/17.19        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 17.02/17.19        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 17.02/17.19      inference('sup-', [status(thm)], ['4', '5'])).
% 17.02/17.19  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('9', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 17.02/17.19      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 17.02/17.19  thf('11', plain,
% 17.02/17.19      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 17.02/17.19            (k2_funct_1 @ sk_B)) @ 
% 17.02/17.19           (k6_relat_1 @ sk_A)))
% 17.02/17.19         <= (~
% 17.02/17.19             ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 17.02/17.19                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 17.02/17.19               (k6_partfun1 @ sk_A))))),
% 17.02/17.19      inference('demod', [status(thm)], ['3', '10'])).
% 17.02/17.19  thf('12', plain,
% 17.02/17.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('13', plain,
% 17.02/17.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf(dt_k2_funct_2, axiom,
% 17.02/17.19    (![A:$i,B:$i]:
% 17.02/17.19     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 17.02/17.19         ( v3_funct_2 @ B @ A @ A ) & 
% 17.02/17.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 17.02/17.19       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 17.02/17.19         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 17.02/17.19         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 17.02/17.19         ( m1_subset_1 @
% 17.02/17.19           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 17.02/17.19  thf('14', plain,
% 17.02/17.19      (![X39 : $i, X40 : $i]:
% 17.02/17.19         ((m1_subset_1 @ (k2_funct_2 @ X39 @ X40) @ 
% 17.02/17.19           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 17.02/17.19          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 17.02/17.19          | ~ (v3_funct_2 @ X40 @ X39 @ X39)
% 17.02/17.19          | ~ (v1_funct_2 @ X40 @ X39 @ X39)
% 17.02/17.19          | ~ (v1_funct_1 @ X40))),
% 17.02/17.19      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 17.02/17.19  thf('15', plain,
% 17.02/17.19      ((~ (v1_funct_1 @ sk_B)
% 17.02/17.19        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 17.02/17.19        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 17.02/17.19        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 17.02/17.19           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 17.02/17.19      inference('sup-', [status(thm)], ['13', '14'])).
% 17.02/17.19  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('17', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('18', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('19', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 17.02/17.19      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 17.02/17.19  thf('20', plain,
% 17.02/17.19      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 17.02/17.19        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.02/17.19      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 17.02/17.19  thf(redefinition_k1_partfun1, axiom,
% 17.02/17.19    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 17.02/17.19     ( ( ( v1_funct_1 @ E ) & 
% 17.02/17.19         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 17.02/17.19         ( v1_funct_1 @ F ) & 
% 17.02/17.19         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 17.02/17.19       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 17.02/17.19  thf('21', plain,
% 17.02/17.19      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 17.02/17.19         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 17.02/17.19          | ~ (v1_funct_1 @ X43)
% 17.02/17.19          | ~ (v1_funct_1 @ X46)
% 17.02/17.19          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 17.02/17.19          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 17.02/17.19              = (k5_relat_1 @ X43 @ X46)))),
% 17.02/17.19      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 17.02/17.19  thf('22', plain,
% 17.02/17.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.02/17.19         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 17.02/17.19            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 17.02/17.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 17.02/17.19          | ~ (v1_funct_1 @ X0)
% 17.02/17.19          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 17.02/17.19      inference('sup-', [status(thm)], ['20', '21'])).
% 17.02/17.19  thf('23', plain,
% 17.02/17.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('24', plain,
% 17.02/17.19      (![X39 : $i, X40 : $i]:
% 17.02/17.19         ((v1_funct_1 @ (k2_funct_2 @ X39 @ X40))
% 17.02/17.19          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 17.02/17.19          | ~ (v3_funct_2 @ X40 @ X39 @ X39)
% 17.02/17.19          | ~ (v1_funct_2 @ X40 @ X39 @ X39)
% 17.02/17.19          | ~ (v1_funct_1 @ X40))),
% 17.02/17.19      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 17.02/17.19  thf('25', plain,
% 17.02/17.19      ((~ (v1_funct_1 @ sk_B)
% 17.02/17.19        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 17.02/17.19        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 17.02/17.19        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 17.02/17.19      inference('sup-', [status(thm)], ['23', '24'])).
% 17.02/17.19  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('27', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('28', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('29', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 17.02/17.19      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 17.02/17.19  thf('30', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 17.02/17.19      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 17.02/17.19  thf('31', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 17.02/17.19      inference('demod', [status(thm)], ['29', '30'])).
% 17.02/17.19  thf('32', plain,
% 17.02/17.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.02/17.19         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 17.02/17.19            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 17.02/17.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 17.02/17.19          | ~ (v1_funct_1 @ X0))),
% 17.02/17.19      inference('demod', [status(thm)], ['22', '31'])).
% 17.02/17.19  thf('33', plain,
% 17.02/17.19      ((~ (v1_funct_1 @ sk_B)
% 17.02/17.19        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 17.02/17.19            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 17.02/17.19      inference('sup-', [status(thm)], ['12', '32'])).
% 17.02/17.19  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('35', plain,
% 17.02/17.19      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 17.02/17.19         = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 17.02/17.19      inference('demod', [status(thm)], ['33', '34'])).
% 17.02/17.19  thf('36', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 17.02/17.19      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 17.02/17.19  thf('37', plain,
% 17.02/17.19      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 17.02/17.19            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 17.02/17.19           (k6_partfun1 @ sk_A)))
% 17.02/17.19         <= (~
% 17.02/17.19             ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 17.02/17.19                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 17.02/17.19               (k6_partfun1 @ sk_A))))),
% 17.02/17.19      inference('split', [status(esa)], ['0'])).
% 17.02/17.19  thf('38', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 17.02/17.19      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 17.02/17.19  thf('39', plain,
% 17.02/17.19      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 17.02/17.19            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 17.02/17.19           (k6_relat_1 @ sk_A)))
% 17.02/17.19         <= (~
% 17.02/17.19             ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 17.02/17.19                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 17.02/17.19               (k6_partfun1 @ sk_A))))),
% 17.02/17.19      inference('demod', [status(thm)], ['37', '38'])).
% 17.02/17.19  thf('40', plain,
% 17.02/17.19      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 17.02/17.19            sk_B) @ 
% 17.02/17.19           (k6_relat_1 @ sk_A)))
% 17.02/17.19         <= (~
% 17.02/17.19             ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 17.02/17.19                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 17.02/17.19               (k6_partfun1 @ sk_A))))),
% 17.02/17.19      inference('sup-', [status(thm)], ['36', '39'])).
% 17.02/17.19  thf('41', plain,
% 17.02/17.19      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19           (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_relat_1 @ sk_A)))
% 17.02/17.19         <= (~
% 17.02/17.19             ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 17.02/17.19                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 17.02/17.19               (k6_partfun1 @ sk_A))))),
% 17.02/17.19      inference('sup-', [status(thm)], ['35', '40'])).
% 17.02/17.19  thf(t61_funct_1, axiom,
% 17.02/17.19    (![A:$i]:
% 17.02/17.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 17.02/17.19       ( ( v2_funct_1 @ A ) =>
% 17.02/17.19         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 17.02/17.19             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 17.02/17.19           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 17.02/17.19             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 17.02/17.19  thf('42', plain,
% 17.02/17.19      (![X12 : $i]:
% 17.02/17.19         (~ (v2_funct_1 @ X12)
% 17.02/17.19          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 17.02/17.19              = (k6_relat_1 @ (k2_relat_1 @ X12)))
% 17.02/17.19          | ~ (v1_funct_1 @ X12)
% 17.02/17.19          | ~ (v1_relat_1 @ X12))),
% 17.02/17.19      inference('cnf', [status(esa)], [t61_funct_1])).
% 17.02/17.19  thf('43', plain,
% 17.02/17.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf(cc2_funct_2, axiom,
% 17.02/17.19    (![A:$i,B:$i,C:$i]:
% 17.02/17.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.02/17.19       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 17.02/17.19         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 17.02/17.19  thf('44', plain,
% 17.02/17.19      (![X26 : $i, X27 : $i, X28 : $i]:
% 17.02/17.19         (~ (v1_funct_1 @ X26)
% 17.02/17.19          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 17.02/17.19          | (v2_funct_2 @ X26 @ X28)
% 17.02/17.19          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 17.02/17.19      inference('cnf', [status(esa)], [cc2_funct_2])).
% 17.02/17.19  thf('45', plain,
% 17.02/17.19      (((v2_funct_2 @ sk_B @ sk_A)
% 17.02/17.19        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 17.02/17.19        | ~ (v1_funct_1 @ sk_B))),
% 17.02/17.19      inference('sup-', [status(thm)], ['43', '44'])).
% 17.02/17.19  thf('46', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('47', plain, ((v1_funct_1 @ sk_B)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('48', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 17.02/17.19      inference('demod', [status(thm)], ['45', '46', '47'])).
% 17.02/17.19  thf(d3_funct_2, axiom,
% 17.02/17.19    (![A:$i,B:$i]:
% 17.02/17.19     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 17.02/17.19       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 17.02/17.19  thf('49', plain,
% 17.02/17.19      (![X37 : $i, X38 : $i]:
% 17.02/17.19         (~ (v2_funct_2 @ X38 @ X37)
% 17.02/17.19          | ((k2_relat_1 @ X38) = (X37))
% 17.02/17.19          | ~ (v5_relat_1 @ X38 @ X37)
% 17.02/17.19          | ~ (v1_relat_1 @ X38))),
% 17.02/17.19      inference('cnf', [status(esa)], [d3_funct_2])).
% 17.02/17.19  thf('50', plain,
% 17.02/17.19      ((~ (v1_relat_1 @ sk_B)
% 17.02/17.19        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 17.02/17.19        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 17.02/17.19      inference('sup-', [status(thm)], ['48', '49'])).
% 17.02/17.19  thf('51', plain,
% 17.02/17.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf(cc1_relset_1, axiom,
% 17.02/17.19    (![A:$i,B:$i,C:$i]:
% 17.02/17.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.02/17.19       ( v1_relat_1 @ C ) ))).
% 17.02/17.19  thf('52', plain,
% 17.02/17.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 17.02/17.19         ((v1_relat_1 @ X13)
% 17.02/17.19          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 17.02/17.19      inference('cnf', [status(esa)], [cc1_relset_1])).
% 17.02/17.19  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 17.02/17.19      inference('sup-', [status(thm)], ['51', '52'])).
% 17.02/17.19  thf('54', plain,
% 17.02/17.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf(cc2_relset_1, axiom,
% 17.02/17.19    (![A:$i,B:$i,C:$i]:
% 17.02/17.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.02/17.19       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 17.02/17.19  thf('55', plain,
% 17.02/17.19      (![X16 : $i, X17 : $i, X18 : $i]:
% 17.02/17.19         ((v5_relat_1 @ X16 @ X18)
% 17.02/17.19          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 17.02/17.19      inference('cnf', [status(esa)], [cc2_relset_1])).
% 17.02/17.19  thf('56', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 17.02/17.19      inference('sup-', [status(thm)], ['54', '55'])).
% 17.02/17.19  thf('57', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 17.02/17.19      inference('demod', [status(thm)], ['50', '53', '56'])).
% 17.02/17.19  thf('58', plain,
% 17.02/17.19      (![X12 : $i]:
% 17.02/17.19         (~ (v2_funct_1 @ X12)
% 17.02/17.19          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 17.02/17.19              = (k6_relat_1 @ (k2_relat_1 @ X12)))
% 17.02/17.19          | ~ (v1_funct_1 @ X12)
% 17.02/17.19          | ~ (v1_relat_1 @ X12))),
% 17.02/17.19      inference('cnf', [status(esa)], [t61_funct_1])).
% 17.02/17.19  thf(dt_k6_partfun1, axiom,
% 17.02/17.19    (![A:$i]:
% 17.02/17.19     ( ( m1_subset_1 @
% 17.02/17.19         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 17.02/17.19       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 17.02/17.19  thf('59', plain,
% 17.02/17.19      (![X42 : $i]:
% 17.02/17.19         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 17.02/17.19          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 17.02/17.19      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 17.02/17.19  thf('60', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 17.02/17.19      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 17.02/17.19  thf('61', plain,
% 17.02/17.19      (![X42 : $i]:
% 17.02/17.19         (m1_subset_1 @ (k6_relat_1 @ X42) @ 
% 17.02/17.19          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 17.02/17.19      inference('demod', [status(thm)], ['59', '60'])).
% 17.02/17.19  thf('62', plain,
% 17.02/17.19      (![X0 : $i]:
% 17.02/17.19         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 17.02/17.19           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 17.02/17.19          | ~ (v1_relat_1 @ X0)
% 17.02/17.19          | ~ (v1_funct_1 @ X0)
% 17.02/17.19          | ~ (v2_funct_1 @ X0))),
% 17.02/17.19      inference('sup+', [status(thm)], ['58', '61'])).
% 17.02/17.19  thf('63', plain,
% 17.02/17.19      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 17.02/17.19         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 17.02/17.19        | ~ (v2_funct_1 @ sk_B)
% 17.02/17.19        | ~ (v1_funct_1 @ sk_B)
% 17.02/17.19        | ~ (v1_relat_1 @ sk_B))),
% 17.02/17.19      inference('sup+', [status(thm)], ['57', '62'])).
% 17.02/17.19  thf('64', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 17.02/17.19      inference('demod', [status(thm)], ['50', '53', '56'])).
% 17.02/17.19  thf('65', plain,
% 17.02/17.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('66', plain,
% 17.02/17.19      (![X26 : $i, X27 : $i, X28 : $i]:
% 17.02/17.19         (~ (v1_funct_1 @ X26)
% 17.02/17.19          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 17.02/17.19          | (v2_funct_1 @ X26)
% 17.02/17.19          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 17.02/17.19      inference('cnf', [status(esa)], [cc2_funct_2])).
% 17.02/17.19  thf('67', plain,
% 17.02/17.19      (((v2_funct_1 @ sk_B)
% 17.02/17.19        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 17.02/17.19        | ~ (v1_funct_1 @ sk_B))),
% 17.02/17.19      inference('sup-', [status(thm)], ['65', '66'])).
% 17.02/17.19  thf('68', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('69', plain, ((v1_funct_1 @ sk_B)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('70', plain, ((v2_funct_1 @ sk_B)),
% 17.02/17.19      inference('demod', [status(thm)], ['67', '68', '69'])).
% 17.02/17.19  thf('71', plain, ((v1_funct_1 @ sk_B)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 17.02/17.19      inference('sup-', [status(thm)], ['51', '52'])).
% 17.02/17.19  thf('73', plain,
% 17.02/17.19      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 17.02/17.19        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.02/17.19      inference('demod', [status(thm)], ['63', '64', '70', '71', '72'])).
% 17.02/17.19  thf(reflexivity_r2_relset_1, axiom,
% 17.02/17.19    (![A:$i,B:$i,C:$i,D:$i]:
% 17.02/17.19     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 17.02/17.19         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 17.02/17.19       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 17.02/17.19  thf('74', plain,
% 17.02/17.19      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 17.02/17.19         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 17.02/17.19          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 17.02/17.19          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 17.02/17.19      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 17.02/17.19  thf('75', plain,
% 17.02/17.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.02/17.19         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 17.02/17.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 17.02/17.19      inference('condensation', [status(thm)], ['74'])).
% 17.02/17.19  thf('76', plain,
% 17.02/17.19      ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 17.02/17.19        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 17.02/17.19      inference('sup-', [status(thm)], ['73', '75'])).
% 17.02/17.19  thf('77', plain,
% 17.02/17.19      (((r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19         (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 17.02/17.19         (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 17.02/17.19        | ~ (v1_relat_1 @ sk_B)
% 17.02/17.19        | ~ (v1_funct_1 @ sk_B)
% 17.02/17.19        | ~ (v2_funct_1 @ sk_B))),
% 17.02/17.19      inference('sup+', [status(thm)], ['42', '76'])).
% 17.02/17.19  thf('78', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 17.02/17.19      inference('demod', [status(thm)], ['50', '53', '56'])).
% 17.02/17.19  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 17.02/17.19      inference('sup-', [status(thm)], ['51', '52'])).
% 17.02/17.19  thf('80', plain, ((v1_funct_1 @ sk_B)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('81', plain, ((v2_funct_1 @ sk_B)),
% 17.02/17.19      inference('demod', [status(thm)], ['67', '68', '69'])).
% 17.02/17.19  thf('82', plain,
% 17.02/17.19      ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_relat_1 @ sk_A))),
% 17.02/17.19      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 17.02/17.19  thf('83', plain,
% 17.02/17.19      (((r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 17.02/17.19          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 17.02/17.19         (k6_partfun1 @ sk_A)))),
% 17.02/17.19      inference('demod', [status(thm)], ['41', '82'])).
% 17.02/17.19  thf('84', plain,
% 17.02/17.19      (~
% 17.02/17.19       ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 17.02/17.19          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 17.02/17.19         (k6_partfun1 @ sk_A))) | 
% 17.02/17.19       ~
% 17.02/17.19       ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 17.02/17.19          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 17.02/17.19         (k6_partfun1 @ sk_A)))),
% 17.02/17.19      inference('split', [status(esa)], ['0'])).
% 17.02/17.19  thf('85', plain,
% 17.02/17.19      (~
% 17.02/17.19       ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 17.02/17.19          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 17.02/17.19         (k6_partfun1 @ sk_A)))),
% 17.02/17.19      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 17.02/17.19  thf('86', plain,
% 17.02/17.19      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 17.02/17.19          (k6_relat_1 @ sk_A))),
% 17.02/17.19      inference('simpl_trail', [status(thm)], ['11', '85'])).
% 17.02/17.19  thf('87', plain,
% 17.02/17.19      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 17.02/17.19        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.02/17.19      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 17.02/17.19  thf('88', plain,
% 17.02/17.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('89', plain,
% 17.02/17.19      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 17.02/17.19         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 17.02/17.19          | ~ (v1_funct_1 @ X43)
% 17.02/17.19          | ~ (v1_funct_1 @ X46)
% 17.02/17.19          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 17.02/17.19          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 17.02/17.19              = (k5_relat_1 @ X43 @ X46)))),
% 17.02/17.19      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 17.02/17.19  thf('90', plain,
% 17.02/17.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.02/17.19         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 17.02/17.19            = (k5_relat_1 @ sk_B @ X0))
% 17.02/17.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 17.02/17.19          | ~ (v1_funct_1 @ X0)
% 17.02/17.19          | ~ (v1_funct_1 @ sk_B))),
% 17.02/17.19      inference('sup-', [status(thm)], ['88', '89'])).
% 17.02/17.19  thf('91', plain, ((v1_funct_1 @ sk_B)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('92', plain,
% 17.02/17.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.02/17.19         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 17.02/17.19            = (k5_relat_1 @ sk_B @ X0))
% 17.02/17.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 17.02/17.19          | ~ (v1_funct_1 @ X0))),
% 17.02/17.19      inference('demod', [status(thm)], ['90', '91'])).
% 17.02/17.19  thf('93', plain,
% 17.02/17.19      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 17.02/17.19        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 17.02/17.19            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 17.02/17.19      inference('sup-', [status(thm)], ['87', '92'])).
% 17.02/17.19  thf('94', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 17.02/17.19      inference('demod', [status(thm)], ['29', '30'])).
% 17.02/17.19  thf('95', plain,
% 17.02/17.19      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 17.02/17.19         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 17.02/17.19      inference('demod', [status(thm)], ['93', '94'])).
% 17.02/17.19  thf('96', plain,
% 17.02/17.19      (![X12 : $i]:
% 17.02/17.19         (~ (v2_funct_1 @ X12)
% 17.02/17.19          | ((k5_relat_1 @ X12 @ (k2_funct_1 @ X12))
% 17.02/17.19              = (k6_relat_1 @ (k1_relat_1 @ X12)))
% 17.02/17.19          | ~ (v1_funct_1 @ X12)
% 17.02/17.19          | ~ (v1_relat_1 @ X12))),
% 17.02/17.19      inference('cnf', [status(esa)], [t61_funct_1])).
% 17.02/17.19  thf('97', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf(d1_funct_2, axiom,
% 17.02/17.19    (![A:$i,B:$i,C:$i]:
% 17.02/17.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.02/17.19       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 17.02/17.19           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 17.02/17.19             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 17.02/17.19         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 17.02/17.19           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 17.02/17.19             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 17.02/17.19  thf(zf_stmt_1, axiom,
% 17.02/17.19    (![C:$i,B:$i,A:$i]:
% 17.02/17.19     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 17.02/17.19       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 17.02/17.19  thf('98', plain,
% 17.02/17.19      (![X31 : $i, X32 : $i, X33 : $i]:
% 17.02/17.19         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 17.02/17.19          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 17.02/17.19          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 17.02/17.19  thf('99', plain,
% 17.02/17.19      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 17.02/17.19        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 17.02/17.19      inference('sup-', [status(thm)], ['97', '98'])).
% 17.02/17.19  thf('100', plain,
% 17.02/17.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 17.02/17.19  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 17.02/17.19  thf(zf_stmt_4, axiom,
% 17.02/17.19    (![B:$i,A:$i]:
% 17.02/17.19     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 17.02/17.19       ( zip_tseitin_0 @ B @ A ) ))).
% 17.02/17.19  thf(zf_stmt_5, axiom,
% 17.02/17.19    (![A:$i,B:$i,C:$i]:
% 17.02/17.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.02/17.19       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 17.02/17.19         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 17.02/17.19           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 17.02/17.19             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 17.02/17.19  thf('101', plain,
% 17.02/17.19      (![X34 : $i, X35 : $i, X36 : $i]:
% 17.02/17.19         (~ (zip_tseitin_0 @ X34 @ X35)
% 17.02/17.19          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 17.02/17.19          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 17.02/17.19  thf('102', plain,
% 17.02/17.19      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 17.02/17.19      inference('sup-', [status(thm)], ['100', '101'])).
% 17.02/17.19  thf('103', plain,
% 17.02/17.19      (![X29 : $i, X30 : $i]:
% 17.02/17.19         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_4])).
% 17.02/17.19  thf('104', plain,
% 17.02/17.19      (![X29 : $i, X30 : $i]:
% 17.02/17.19         ((zip_tseitin_0 @ X29 @ X30) | ((X30) != (k1_xboole_0)))),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_4])).
% 17.02/17.19  thf('105', plain, (![X29 : $i]: (zip_tseitin_0 @ X29 @ k1_xboole_0)),
% 17.02/17.19      inference('simplify', [status(thm)], ['104'])).
% 17.02/17.19  thf('106', plain,
% 17.02/17.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.02/17.19         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 17.02/17.19      inference('sup+', [status(thm)], ['103', '105'])).
% 17.02/17.19  thf('107', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 17.02/17.19      inference('eq_fact', [status(thm)], ['106'])).
% 17.02/17.19  thf('108', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 17.02/17.19      inference('demod', [status(thm)], ['102', '107'])).
% 17.02/17.19  thf('109', plain,
% 17.02/17.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf(redefinition_k1_relset_1, axiom,
% 17.02/17.19    (![A:$i,B:$i,C:$i]:
% 17.02/17.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.02/17.19       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 17.02/17.19  thf('110', plain,
% 17.02/17.19      (![X19 : $i, X20 : $i, X21 : $i]:
% 17.02/17.19         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 17.02/17.19          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 17.02/17.19      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 17.02/17.19  thf('111', plain,
% 17.02/17.19      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 17.02/17.19      inference('sup-', [status(thm)], ['109', '110'])).
% 17.02/17.19  thf('112', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 17.02/17.19      inference('demod', [status(thm)], ['99', '108', '111'])).
% 17.02/17.19  thf('113', plain,
% 17.02/17.19      (![X12 : $i]:
% 17.02/17.19         (~ (v2_funct_1 @ X12)
% 17.02/17.19          | ((k5_relat_1 @ X12 @ (k2_funct_1 @ X12))
% 17.02/17.19              = (k6_relat_1 @ (k1_relat_1 @ X12)))
% 17.02/17.19          | ~ (v1_funct_1 @ X12)
% 17.02/17.19          | ~ (v1_relat_1 @ X12))),
% 17.02/17.19      inference('cnf', [status(esa)], [t61_funct_1])).
% 17.02/17.19  thf('114', plain,
% 17.02/17.19      (![X42 : $i]:
% 17.02/17.19         (m1_subset_1 @ (k6_relat_1 @ X42) @ 
% 17.02/17.19          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 17.02/17.19      inference('demod', [status(thm)], ['59', '60'])).
% 17.02/17.19  thf('115', plain,
% 17.02/17.19      (![X0 : $i]:
% 17.02/17.19         ((m1_subset_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 17.02/17.19           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 17.02/17.19          | ~ (v1_relat_1 @ X0)
% 17.02/17.19          | ~ (v1_funct_1 @ X0)
% 17.02/17.19          | ~ (v2_funct_1 @ X0))),
% 17.02/17.19      inference('sup+', [status(thm)], ['113', '114'])).
% 17.02/17.19  thf('116', plain,
% 17.02/17.19      (((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 17.02/17.19         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 17.02/17.19        | ~ (v2_funct_1 @ sk_B)
% 17.02/17.19        | ~ (v1_funct_1 @ sk_B)
% 17.02/17.19        | ~ (v1_relat_1 @ sk_B))),
% 17.02/17.19      inference('sup+', [status(thm)], ['112', '115'])).
% 17.02/17.19  thf('117', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 17.02/17.19      inference('demod', [status(thm)], ['99', '108', '111'])).
% 17.02/17.19  thf('118', plain, ((v2_funct_1 @ sk_B)),
% 17.02/17.19      inference('demod', [status(thm)], ['67', '68', '69'])).
% 17.02/17.19  thf('119', plain, ((v1_funct_1 @ sk_B)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('120', plain, ((v1_relat_1 @ sk_B)),
% 17.02/17.19      inference('sup-', [status(thm)], ['51', '52'])).
% 17.02/17.19  thf('121', plain,
% 17.02/17.19      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 17.02/17.19        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.02/17.19      inference('demod', [status(thm)], ['116', '117', '118', '119', '120'])).
% 17.02/17.19  thf('122', plain,
% 17.02/17.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.02/17.19         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 17.02/17.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 17.02/17.19      inference('condensation', [status(thm)], ['74'])).
% 17.02/17.19  thf('123', plain,
% 17.02/17.19      ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19        (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 17.02/17.19        (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 17.02/17.19      inference('sup-', [status(thm)], ['121', '122'])).
% 17.02/17.19  thf('124', plain,
% 17.02/17.19      (((r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19         (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 17.02/17.19         (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 17.02/17.19        | ~ (v1_relat_1 @ sk_B)
% 17.02/17.19        | ~ (v1_funct_1 @ sk_B)
% 17.02/17.19        | ~ (v2_funct_1 @ sk_B))),
% 17.02/17.19      inference('sup+', [status(thm)], ['96', '123'])).
% 17.02/17.19  thf('125', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 17.02/17.19      inference('demod', [status(thm)], ['99', '108', '111'])).
% 17.02/17.19  thf('126', plain, ((v1_relat_1 @ sk_B)),
% 17.02/17.19      inference('sup-', [status(thm)], ['51', '52'])).
% 17.02/17.19  thf('127', plain, ((v1_funct_1 @ sk_B)),
% 17.02/17.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.02/17.19  thf('128', plain, ((v2_funct_1 @ sk_B)),
% 17.02/17.19      inference('demod', [status(thm)], ['67', '68', '69'])).
% 17.02/17.19  thf('129', plain,
% 17.02/17.19      ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.02/17.19        (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A))),
% 17.02/17.19      inference('demod', [status(thm)], ['124', '125', '126', '127', '128'])).
% 17.02/17.19  thf('130', plain, ($false),
% 17.02/17.19      inference('demod', [status(thm)], ['86', '95', '129'])).
% 17.02/17.19  
% 17.02/17.19  % SZS output end Refutation
% 17.02/17.19  
% 17.02/17.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
