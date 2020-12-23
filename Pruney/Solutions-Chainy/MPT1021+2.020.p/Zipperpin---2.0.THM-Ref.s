%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zWLHei1kIK

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:13 EST 2020

% Result     : Theorem 35.62s
% Output     : Refutation 35.62s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 536 expanded)
%              Number of leaves         :   46 ( 180 expanded)
%              Depth                    :   15
%              Number of atoms          : 1668 (11372 expanded)
%              Number of equality atoms :   57 ( 125 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ! [X45: $i,X46: $i] :
      ( ( ( k2_funct_2 @ X46 @ X45 )
        = ( k2_funct_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) )
      | ~ ( v3_funct_2 @ X45 @ X46 @ X46 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X46 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B_1 )
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v3_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('20',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v3_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('31',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','31'])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('37',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('39',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
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
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X7 ) @ X7 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('43',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_2 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('45',plain,
    ( ( v2_funct_2 @ sk_B_1 @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_funct_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['45','46','47'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('49',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v2_funct_2 @ X33 @ X32 )
      | ( ( k2_relat_1 @ X33 )
        = X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v5_relat_1 @ sk_B_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('52',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('53',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('55',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('56',plain,(
    v5_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['50','53','56'])).

thf('58',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X7 ) @ X7 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('59',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('60',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('61',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['57','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['50','53','56'])).

thf('65',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('67',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('73',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','70','71','72'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('74',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['74'])).

thf('76',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['42','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['50','53','56'])).

thf('79',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('80',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('82',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['41','82'])).

thf('84',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('85',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','85'])).

thf('87',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('88',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('95',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X7 @ ( k2_funct_1 @ X7 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('97',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('99',plain,
    ( ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('101',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('102',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['99','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('105',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('106',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('108',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('109',plain,(
    ! [X24: $i] :
      ( zip_tseitin_0 @ X24 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['107','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['110'])).

thf('112',plain,(
    zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['106','111'])).

thf('113',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['103','112'])).

thf('114',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X7 @ ( k2_funct_1 @ X7 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('115',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ) )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['113','116'])).

thf('118',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['103','112'])).

thf('119',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('120',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('122',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['74'])).

thf('124',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['96','124'])).

thf('126',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['103','112'])).

thf('127',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('128',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('130',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['125','126','127','128','129'])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['86','95','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zWLHei1kIK
% 0.12/0.36  % Computer   : n004.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 13:13:39 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 35.62/35.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 35.62/35.85  % Solved by: fo/fo7.sh
% 35.62/35.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 35.62/35.85  % done 6466 iterations in 35.408s
% 35.62/35.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 35.62/35.85  % SZS output start Refutation
% 35.62/35.85  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 35.62/35.85  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 35.62/35.85  thf(sk_A_type, type, sk_A: $i).
% 35.62/35.85  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 35.62/35.85  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 35.62/35.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 35.62/35.85  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 35.62/35.85  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 35.62/35.85  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 35.62/35.85  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 35.62/35.85  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 35.62/35.85  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 35.62/35.85  thf(sk_B_1_type, type, sk_B_1: $i).
% 35.62/35.85  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 35.62/35.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 35.62/35.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 35.62/35.85  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 35.62/35.85  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 35.62/35.85  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 35.62/35.85  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 35.62/35.85  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 35.62/35.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 35.62/35.85  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 35.62/35.85  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 35.62/35.85  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 35.62/35.85  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 35.62/35.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 35.62/35.85  thf(t88_funct_2, conjecture,
% 35.62/35.85    (![A:$i,B:$i]:
% 35.62/35.85     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 35.62/35.85         ( v3_funct_2 @ B @ A @ A ) & 
% 35.62/35.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 35.62/35.85       ( ( r2_relset_1 @
% 35.62/35.85           A @ A @ 
% 35.62/35.85           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 35.62/35.85           ( k6_partfun1 @ A ) ) & 
% 35.62/35.85         ( r2_relset_1 @
% 35.62/35.85           A @ A @ 
% 35.62/35.85           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 35.62/35.85           ( k6_partfun1 @ A ) ) ) ))).
% 35.62/35.85  thf(zf_stmt_0, negated_conjecture,
% 35.62/35.85    (~( ![A:$i,B:$i]:
% 35.62/35.85        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 35.62/35.85            ( v3_funct_2 @ B @ A @ A ) & 
% 35.62/35.85            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 35.62/35.85          ( ( r2_relset_1 @
% 35.62/35.85              A @ A @ 
% 35.62/35.85              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 35.62/35.85              ( k6_partfun1 @ A ) ) & 
% 35.62/35.85            ( r2_relset_1 @
% 35.62/35.85              A @ A @ 
% 35.62/35.85              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 35.62/35.85              ( k6_partfun1 @ A ) ) ) ) )),
% 35.62/35.85    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 35.62/35.85  thf('0', plain,
% 35.62/35.85      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 35.62/35.85            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 35.62/35.85           (k6_partfun1 @ sk_A))
% 35.62/35.85        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 35.62/35.85              (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 35.62/35.85             (k6_partfun1 @ sk_A)))),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('1', plain,
% 35.62/35.85      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 35.62/35.85            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 35.62/35.85           (k6_partfun1 @ sk_A)))
% 35.62/35.85         <= (~
% 35.62/35.85             ((r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 35.62/35.85                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 35.62/35.85               (k6_partfun1 @ sk_A))))),
% 35.62/35.85      inference('split', [status(esa)], ['0'])).
% 35.62/35.85  thf(redefinition_k6_partfun1, axiom,
% 35.62/35.85    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 35.62/35.85  thf('2', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 35.62/35.85      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 35.62/35.85  thf('3', plain,
% 35.62/35.85      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 35.62/35.85            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 35.62/35.85           (k6_relat_1 @ sk_A)))
% 35.62/35.85         <= (~
% 35.62/35.85             ((r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 35.62/35.85                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 35.62/35.85               (k6_partfun1 @ sk_A))))),
% 35.62/35.85      inference('demod', [status(thm)], ['1', '2'])).
% 35.62/35.85  thf('4', plain,
% 35.62/35.85      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf(redefinition_k2_funct_2, axiom,
% 35.62/35.85    (![A:$i,B:$i]:
% 35.62/35.85     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 35.62/35.85         ( v3_funct_2 @ B @ A @ A ) & 
% 35.62/35.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 35.62/35.85       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 35.62/35.85  thf('5', plain,
% 35.62/35.85      (![X45 : $i, X46 : $i]:
% 35.62/35.85         (((k2_funct_2 @ X46 @ X45) = (k2_funct_1 @ X45))
% 35.62/35.85          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X46)))
% 35.62/35.85          | ~ (v3_funct_2 @ X45 @ X46 @ X46)
% 35.62/35.85          | ~ (v1_funct_2 @ X45 @ X46 @ X46)
% 35.62/35.85          | ~ (v1_funct_1 @ X45))),
% 35.62/35.85      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 35.62/35.85  thf('6', plain,
% 35.62/35.85      ((~ (v1_funct_1 @ sk_B_1)
% 35.62/35.85        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 35.62/35.85        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 35.62/35.85        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 35.62/35.85      inference('sup-', [status(thm)], ['4', '5'])).
% 35.62/35.85  thf('7', plain, ((v1_funct_1 @ sk_B_1)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('8', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('9', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 35.62/35.85      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 35.62/35.85  thf('11', plain,
% 35.62/35.85      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 35.62/35.85            (k2_funct_1 @ sk_B_1)) @ 
% 35.62/35.85           (k6_relat_1 @ sk_A)))
% 35.62/35.85         <= (~
% 35.62/35.85             ((r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 35.62/35.85                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 35.62/35.85               (k6_partfun1 @ sk_A))))),
% 35.62/35.85      inference('demod', [status(thm)], ['3', '10'])).
% 35.62/35.85  thf('12', plain,
% 35.62/35.85      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('13', plain,
% 35.62/35.85      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf(dt_k2_funct_2, axiom,
% 35.62/35.85    (![A:$i,B:$i]:
% 35.62/35.85     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 35.62/35.85         ( v3_funct_2 @ B @ A @ A ) & 
% 35.62/35.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 35.62/35.85       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 35.62/35.85         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 35.62/35.85         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 35.62/35.85         ( m1_subset_1 @
% 35.62/35.85           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 35.62/35.85  thf('14', plain,
% 35.62/35.85      (![X34 : $i, X35 : $i]:
% 35.62/35.85         ((m1_subset_1 @ (k2_funct_2 @ X34 @ X35) @ 
% 35.62/35.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 35.62/35.85          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 35.62/35.85          | ~ (v3_funct_2 @ X35 @ X34 @ X34)
% 35.62/35.85          | ~ (v1_funct_2 @ X35 @ X34 @ X34)
% 35.62/35.85          | ~ (v1_funct_1 @ X35))),
% 35.62/35.85      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 35.62/35.85  thf('15', plain,
% 35.62/35.85      ((~ (v1_funct_1 @ sk_B_1)
% 35.62/35.85        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 35.62/35.85        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 35.62/35.85        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 35.62/35.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 35.62/35.85      inference('sup-', [status(thm)], ['13', '14'])).
% 35.62/35.85  thf('16', plain, ((v1_funct_1 @ sk_B_1)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('17', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('18', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('19', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 35.62/35.85      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 35.62/35.85  thf('20', plain,
% 35.62/35.85      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 35.62/35.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 35.62/35.85      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 35.62/35.85  thf(redefinition_k1_partfun1, axiom,
% 35.62/35.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 35.62/35.85     ( ( ( v1_funct_1 @ E ) & 
% 35.62/35.85         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 35.62/35.85         ( v1_funct_1 @ F ) & 
% 35.62/35.85         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 35.62/35.85       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 35.62/35.85  thf('21', plain,
% 35.62/35.85      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 35.62/35.85         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 35.62/35.85          | ~ (v1_funct_1 @ X39)
% 35.62/35.85          | ~ (v1_funct_1 @ X42)
% 35.62/35.85          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 35.62/35.85          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 35.62/35.85              = (k5_relat_1 @ X39 @ X42)))),
% 35.62/35.85      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 35.62/35.85  thf('22', plain,
% 35.62/35.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.62/35.85         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B_1) @ X0)
% 35.62/35.85            = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ X0))
% 35.62/35.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 35.62/35.85          | ~ (v1_funct_1 @ X0)
% 35.62/35.85          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 35.62/35.85      inference('sup-', [status(thm)], ['20', '21'])).
% 35.62/35.85  thf('23', plain,
% 35.62/35.85      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('24', plain,
% 35.62/35.85      (![X34 : $i, X35 : $i]:
% 35.62/35.85         ((v1_funct_1 @ (k2_funct_2 @ X34 @ X35))
% 35.62/35.85          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 35.62/35.85          | ~ (v3_funct_2 @ X35 @ X34 @ X34)
% 35.62/35.85          | ~ (v1_funct_2 @ X35 @ X34 @ X34)
% 35.62/35.85          | ~ (v1_funct_1 @ X35))),
% 35.62/35.85      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 35.62/35.85  thf('25', plain,
% 35.62/35.85      ((~ (v1_funct_1 @ sk_B_1)
% 35.62/35.85        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 35.62/35.85        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 35.62/35.85        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1)))),
% 35.62/35.85      inference('sup-', [status(thm)], ['23', '24'])).
% 35.62/35.85  thf('26', plain, ((v1_funct_1 @ sk_B_1)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('27', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('28', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('29', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 35.62/35.85      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 35.62/35.85  thf('30', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 35.62/35.85      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 35.62/35.85  thf('31', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 35.62/35.85      inference('demod', [status(thm)], ['29', '30'])).
% 35.62/35.85  thf('32', plain,
% 35.62/35.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.62/35.85         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B_1) @ X0)
% 35.62/35.85            = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ X0))
% 35.62/35.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 35.62/35.85          | ~ (v1_funct_1 @ X0))),
% 35.62/35.85      inference('demod', [status(thm)], ['22', '31'])).
% 35.62/35.85  thf('33', plain,
% 35.62/35.85      ((~ (v1_funct_1 @ sk_B_1)
% 35.62/35.85        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 35.62/35.85            sk_B_1) = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1)))),
% 35.62/35.85      inference('sup-', [status(thm)], ['12', '32'])).
% 35.62/35.85  thf('34', plain, ((v1_funct_1 @ sk_B_1)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('35', plain,
% 35.62/35.85      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 35.62/35.85         sk_B_1) = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1))),
% 35.62/35.85      inference('demod', [status(thm)], ['33', '34'])).
% 35.62/35.85  thf('36', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 35.62/35.85      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 35.62/35.85  thf('37', plain,
% 35.62/35.85      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 35.62/35.85            (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 35.62/35.85           (k6_partfun1 @ sk_A)))
% 35.62/35.85         <= (~
% 35.62/35.85             ((r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 35.62/35.85                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 35.62/35.85               (k6_partfun1 @ sk_A))))),
% 35.62/35.85      inference('split', [status(esa)], ['0'])).
% 35.62/35.85  thf('38', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 35.62/35.85      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 35.62/35.85  thf('39', plain,
% 35.62/35.85      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 35.62/35.85            (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 35.62/35.85           (k6_relat_1 @ sk_A)))
% 35.62/35.85         <= (~
% 35.62/35.85             ((r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 35.62/35.85                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 35.62/35.85               (k6_partfun1 @ sk_A))))),
% 35.62/35.85      inference('demod', [status(thm)], ['37', '38'])).
% 35.62/35.85  thf('40', plain,
% 35.62/35.85      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 35.62/35.85            sk_B_1) @ 
% 35.62/35.85           (k6_relat_1 @ sk_A)))
% 35.62/35.85         <= (~
% 35.62/35.85             ((r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 35.62/35.85                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 35.62/35.85               (k6_partfun1 @ sk_A))))),
% 35.62/35.85      inference('sup-', [status(thm)], ['36', '39'])).
% 35.62/35.85  thf('41', plain,
% 35.62/35.85      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85           (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ (k6_relat_1 @ sk_A)))
% 35.62/35.85         <= (~
% 35.62/35.85             ((r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 35.62/35.85                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 35.62/35.85               (k6_partfun1 @ sk_A))))),
% 35.62/35.85      inference('sup-', [status(thm)], ['35', '40'])).
% 35.62/35.85  thf(t61_funct_1, axiom,
% 35.62/35.85    (![A:$i]:
% 35.62/35.85     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 35.62/35.85       ( ( v2_funct_1 @ A ) =>
% 35.62/35.85         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 35.62/35.85             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 35.62/35.85           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 35.62/35.85             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 35.62/35.85  thf('42', plain,
% 35.62/35.85      (![X7 : $i]:
% 35.62/35.85         (~ (v2_funct_1 @ X7)
% 35.62/35.85          | ((k5_relat_1 @ (k2_funct_1 @ X7) @ X7)
% 35.62/35.85              = (k6_relat_1 @ (k2_relat_1 @ X7)))
% 35.62/35.85          | ~ (v1_funct_1 @ X7)
% 35.62/35.85          | ~ (v1_relat_1 @ X7))),
% 35.62/35.85      inference('cnf', [status(esa)], [t61_funct_1])).
% 35.62/35.85  thf('43', plain,
% 35.62/35.85      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf(cc2_funct_2, axiom,
% 35.62/35.85    (![A:$i,B:$i,C:$i]:
% 35.62/35.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 35.62/35.85       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 35.62/35.85         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 35.62/35.85  thf('44', plain,
% 35.62/35.85      (![X21 : $i, X22 : $i, X23 : $i]:
% 35.62/35.85         (~ (v1_funct_1 @ X21)
% 35.62/35.85          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 35.62/35.85          | (v2_funct_2 @ X21 @ X23)
% 35.62/35.85          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 35.62/35.85      inference('cnf', [status(esa)], [cc2_funct_2])).
% 35.62/35.85  thf('45', plain,
% 35.62/35.85      (((v2_funct_2 @ sk_B_1 @ sk_A)
% 35.62/35.85        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 35.62/35.85        | ~ (v1_funct_1 @ sk_B_1))),
% 35.62/35.85      inference('sup-', [status(thm)], ['43', '44'])).
% 35.62/35.85  thf('46', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('47', plain, ((v1_funct_1 @ sk_B_1)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('48', plain, ((v2_funct_2 @ sk_B_1 @ sk_A)),
% 35.62/35.85      inference('demod', [status(thm)], ['45', '46', '47'])).
% 35.62/35.85  thf(d3_funct_2, axiom,
% 35.62/35.85    (![A:$i,B:$i]:
% 35.62/35.85     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 35.62/35.85       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 35.62/35.85  thf('49', plain,
% 35.62/35.85      (![X32 : $i, X33 : $i]:
% 35.62/35.85         (~ (v2_funct_2 @ X33 @ X32)
% 35.62/35.85          | ((k2_relat_1 @ X33) = (X32))
% 35.62/35.85          | ~ (v5_relat_1 @ X33 @ X32)
% 35.62/35.85          | ~ (v1_relat_1 @ X33))),
% 35.62/35.85      inference('cnf', [status(esa)], [d3_funct_2])).
% 35.62/35.85  thf('50', plain,
% 35.62/35.85      ((~ (v1_relat_1 @ sk_B_1)
% 35.62/35.85        | ~ (v5_relat_1 @ sk_B_1 @ sk_A)
% 35.62/35.85        | ((k2_relat_1 @ sk_B_1) = (sk_A)))),
% 35.62/35.85      inference('sup-', [status(thm)], ['48', '49'])).
% 35.62/35.85  thf('51', plain,
% 35.62/35.85      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf(cc1_relset_1, axiom,
% 35.62/35.85    (![A:$i,B:$i,C:$i]:
% 35.62/35.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 35.62/35.85       ( v1_relat_1 @ C ) ))).
% 35.62/35.85  thf('52', plain,
% 35.62/35.85      (![X8 : $i, X9 : $i, X10 : $i]:
% 35.62/35.85         ((v1_relat_1 @ X8)
% 35.62/35.85          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 35.62/35.85      inference('cnf', [status(esa)], [cc1_relset_1])).
% 35.62/35.85  thf('53', plain, ((v1_relat_1 @ sk_B_1)),
% 35.62/35.85      inference('sup-', [status(thm)], ['51', '52'])).
% 35.62/35.85  thf('54', plain,
% 35.62/35.85      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf(cc2_relset_1, axiom,
% 35.62/35.85    (![A:$i,B:$i,C:$i]:
% 35.62/35.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 35.62/35.85       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 35.62/35.85  thf('55', plain,
% 35.62/35.85      (![X11 : $i, X12 : $i, X13 : $i]:
% 35.62/35.85         ((v5_relat_1 @ X11 @ X13)
% 35.62/35.85          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 35.62/35.85      inference('cnf', [status(esa)], [cc2_relset_1])).
% 35.62/35.85  thf('56', plain, ((v5_relat_1 @ sk_B_1 @ sk_A)),
% 35.62/35.85      inference('sup-', [status(thm)], ['54', '55'])).
% 35.62/35.85  thf('57', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 35.62/35.85      inference('demod', [status(thm)], ['50', '53', '56'])).
% 35.62/35.85  thf('58', plain,
% 35.62/35.85      (![X7 : $i]:
% 35.62/35.85         (~ (v2_funct_1 @ X7)
% 35.62/35.85          | ((k5_relat_1 @ (k2_funct_1 @ X7) @ X7)
% 35.62/35.85              = (k6_relat_1 @ (k2_relat_1 @ X7)))
% 35.62/35.85          | ~ (v1_funct_1 @ X7)
% 35.62/35.85          | ~ (v1_relat_1 @ X7))),
% 35.62/35.85      inference('cnf', [status(esa)], [t61_funct_1])).
% 35.62/35.85  thf(dt_k6_partfun1, axiom,
% 35.62/35.85    (![A:$i]:
% 35.62/35.85     ( ( m1_subset_1 @
% 35.62/35.85         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 35.62/35.85       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 35.62/35.85  thf('59', plain,
% 35.62/35.85      (![X37 : $i]:
% 35.62/35.85         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 35.62/35.85          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 35.62/35.85      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 35.62/35.85  thf('60', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 35.62/35.85      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 35.62/35.85  thf('61', plain,
% 35.62/35.85      (![X37 : $i]:
% 35.62/35.85         (m1_subset_1 @ (k6_relat_1 @ X37) @ 
% 35.62/35.85          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 35.62/35.85      inference('demod', [status(thm)], ['59', '60'])).
% 35.62/35.85  thf('62', plain,
% 35.62/35.85      (![X0 : $i]:
% 35.62/35.85         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 35.62/35.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 35.62/35.85          | ~ (v1_relat_1 @ X0)
% 35.62/35.85          | ~ (v1_funct_1 @ X0)
% 35.62/35.85          | ~ (v2_funct_1 @ X0))),
% 35.62/35.85      inference('sup+', [status(thm)], ['58', '61'])).
% 35.62/35.85  thf('63', plain,
% 35.62/35.85      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 35.62/35.85         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B_1))))
% 35.62/35.85        | ~ (v2_funct_1 @ sk_B_1)
% 35.62/35.85        | ~ (v1_funct_1 @ sk_B_1)
% 35.62/35.85        | ~ (v1_relat_1 @ sk_B_1))),
% 35.62/35.85      inference('sup+', [status(thm)], ['57', '62'])).
% 35.62/35.85  thf('64', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 35.62/35.85      inference('demod', [status(thm)], ['50', '53', '56'])).
% 35.62/35.85  thf('65', plain,
% 35.62/35.85      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('66', plain,
% 35.62/35.85      (![X21 : $i, X22 : $i, X23 : $i]:
% 35.62/35.85         (~ (v1_funct_1 @ X21)
% 35.62/35.85          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 35.62/35.85          | (v2_funct_1 @ X21)
% 35.62/35.85          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 35.62/35.85      inference('cnf', [status(esa)], [cc2_funct_2])).
% 35.62/35.85  thf('67', plain,
% 35.62/35.85      (((v2_funct_1 @ sk_B_1)
% 35.62/35.85        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 35.62/35.85        | ~ (v1_funct_1 @ sk_B_1))),
% 35.62/35.85      inference('sup-', [status(thm)], ['65', '66'])).
% 35.62/35.85  thf('68', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('69', plain, ((v1_funct_1 @ sk_B_1)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('70', plain, ((v2_funct_1 @ sk_B_1)),
% 35.62/35.85      inference('demod', [status(thm)], ['67', '68', '69'])).
% 35.62/35.85  thf('71', plain, ((v1_funct_1 @ sk_B_1)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('72', plain, ((v1_relat_1 @ sk_B_1)),
% 35.62/35.85      inference('sup-', [status(thm)], ['51', '52'])).
% 35.62/35.85  thf('73', plain,
% 35.62/35.85      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 35.62/35.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 35.62/35.85      inference('demod', [status(thm)], ['63', '64', '70', '71', '72'])).
% 35.62/35.85  thf(reflexivity_r2_relset_1, axiom,
% 35.62/35.85    (![A:$i,B:$i,C:$i,D:$i]:
% 35.62/35.85     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 35.62/35.85         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 35.62/35.85       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 35.62/35.85  thf('74', plain,
% 35.62/35.85      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 35.62/35.85         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 35.62/35.85          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 35.62/35.85          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 35.62/35.85      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 35.62/35.85  thf('75', plain,
% 35.62/35.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.62/35.85         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 35.62/35.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 35.62/35.85      inference('condensation', [status(thm)], ['74'])).
% 35.62/35.85  thf('76', plain,
% 35.62/35.85      ((r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85        (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 35.62/35.85        (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1))),
% 35.62/35.85      inference('sup-', [status(thm)], ['73', '75'])).
% 35.62/35.85  thf('77', plain,
% 35.62/35.85      (((r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85         (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 35.62/35.85         (k6_relat_1 @ (k2_relat_1 @ sk_B_1)))
% 35.62/35.85        | ~ (v1_relat_1 @ sk_B_1)
% 35.62/35.85        | ~ (v1_funct_1 @ sk_B_1)
% 35.62/35.85        | ~ (v2_funct_1 @ sk_B_1))),
% 35.62/35.85      inference('sup+', [status(thm)], ['42', '76'])).
% 35.62/35.85  thf('78', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 35.62/35.85      inference('demod', [status(thm)], ['50', '53', '56'])).
% 35.62/35.85  thf('79', plain, ((v1_relat_1 @ sk_B_1)),
% 35.62/35.85      inference('sup-', [status(thm)], ['51', '52'])).
% 35.62/35.85  thf('80', plain, ((v1_funct_1 @ sk_B_1)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('81', plain, ((v2_funct_1 @ sk_B_1)),
% 35.62/35.85      inference('demod', [status(thm)], ['67', '68', '69'])).
% 35.62/35.85  thf('82', plain,
% 35.62/35.85      ((r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85        (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ (k6_relat_1 @ sk_A))),
% 35.62/35.85      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 35.62/35.85  thf('83', plain,
% 35.62/35.85      (((r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 35.62/35.85          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 35.62/35.85         (k6_partfun1 @ sk_A)))),
% 35.62/35.85      inference('demod', [status(thm)], ['41', '82'])).
% 35.62/35.85  thf('84', plain,
% 35.62/35.85      (~
% 35.62/35.85       ((r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 35.62/35.85          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 35.62/35.85         (k6_partfun1 @ sk_A))) | 
% 35.62/35.85       ~
% 35.62/35.85       ((r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 35.62/35.85          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 35.62/35.85         (k6_partfun1 @ sk_A)))),
% 35.62/35.85      inference('split', [status(esa)], ['0'])).
% 35.62/35.85  thf('85', plain,
% 35.62/35.85      (~
% 35.62/35.85       ((r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 35.62/35.85          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 35.62/35.85         (k6_partfun1 @ sk_A)))),
% 35.62/35.85      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 35.62/35.85  thf('86', plain,
% 35.62/35.85      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 35.62/35.85           (k2_funct_1 @ sk_B_1)) @ 
% 35.62/35.85          (k6_relat_1 @ sk_A))),
% 35.62/35.85      inference('simpl_trail', [status(thm)], ['11', '85'])).
% 35.62/35.85  thf('87', plain,
% 35.62/35.85      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 35.62/35.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 35.62/35.85      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 35.62/35.85  thf('88', plain,
% 35.62/35.85      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('89', plain,
% 35.62/35.85      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 35.62/35.85         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 35.62/35.85          | ~ (v1_funct_1 @ X39)
% 35.62/35.85          | ~ (v1_funct_1 @ X42)
% 35.62/35.85          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 35.62/35.85          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 35.62/35.85              = (k5_relat_1 @ X39 @ X42)))),
% 35.62/35.85      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 35.62/35.85  thf('90', plain,
% 35.62/35.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.62/35.85         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 35.62/35.85            = (k5_relat_1 @ sk_B_1 @ X0))
% 35.62/35.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 35.62/35.85          | ~ (v1_funct_1 @ X0)
% 35.62/35.85          | ~ (v1_funct_1 @ sk_B_1))),
% 35.62/35.85      inference('sup-', [status(thm)], ['88', '89'])).
% 35.62/35.85  thf('91', plain, ((v1_funct_1 @ sk_B_1)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('92', plain,
% 35.62/35.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.62/35.85         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 35.62/35.85            = (k5_relat_1 @ sk_B_1 @ X0))
% 35.62/35.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 35.62/35.85          | ~ (v1_funct_1 @ X0))),
% 35.62/35.85      inference('demod', [status(thm)], ['90', '91'])).
% 35.62/35.85  thf('93', plain,
% 35.62/35.85      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 35.62/35.85        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 35.62/35.85            (k2_funct_1 @ sk_B_1))
% 35.62/35.85            = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))))),
% 35.62/35.85      inference('sup-', [status(thm)], ['87', '92'])).
% 35.62/35.85  thf('94', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 35.62/35.85      inference('demod', [status(thm)], ['29', '30'])).
% 35.62/35.85  thf('95', plain,
% 35.62/35.85      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 35.62/35.85         (k2_funct_1 @ sk_B_1)) = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)))),
% 35.62/35.85      inference('demod', [status(thm)], ['93', '94'])).
% 35.62/35.85  thf('96', plain,
% 35.62/35.85      (![X7 : $i]:
% 35.62/35.85         (~ (v2_funct_1 @ X7)
% 35.62/35.85          | ((k5_relat_1 @ X7 @ (k2_funct_1 @ X7))
% 35.62/35.85              = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 35.62/35.85          | ~ (v1_funct_1 @ X7)
% 35.62/35.85          | ~ (v1_relat_1 @ X7))),
% 35.62/35.85      inference('cnf', [status(esa)], [t61_funct_1])).
% 35.62/35.85  thf('97', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf(d1_funct_2, axiom,
% 35.62/35.85    (![A:$i,B:$i,C:$i]:
% 35.62/35.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 35.62/35.85       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 35.62/35.85           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 35.62/35.85             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 35.62/35.85         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 35.62/35.85           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 35.62/35.85             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 35.62/35.85  thf(zf_stmt_1, axiom,
% 35.62/35.85    (![C:$i,B:$i,A:$i]:
% 35.62/35.85     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 35.62/35.85       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 35.62/35.85  thf('98', plain,
% 35.62/35.85      (![X26 : $i, X27 : $i, X28 : $i]:
% 35.62/35.85         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 35.62/35.85          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 35.62/35.85          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_1])).
% 35.62/35.85  thf('99', plain,
% 35.62/35.85      ((~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A)
% 35.62/35.85        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B_1)))),
% 35.62/35.85      inference('sup-', [status(thm)], ['97', '98'])).
% 35.62/35.85  thf('100', plain,
% 35.62/35.85      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf(redefinition_k1_relset_1, axiom,
% 35.62/35.85    (![A:$i,B:$i,C:$i]:
% 35.62/35.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 35.62/35.85       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 35.62/35.85  thf('101', plain,
% 35.62/35.85      (![X14 : $i, X15 : $i, X16 : $i]:
% 35.62/35.85         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 35.62/35.85          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 35.62/35.85      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 35.62/35.85  thf('102', plain,
% 35.62/35.85      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 35.62/35.85      inference('sup-', [status(thm)], ['100', '101'])).
% 35.62/35.85  thf('103', plain,
% 35.62/35.85      ((~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A)
% 35.62/35.85        | ((sk_A) = (k1_relat_1 @ sk_B_1)))),
% 35.62/35.85      inference('demod', [status(thm)], ['99', '102'])).
% 35.62/35.85  thf('104', plain,
% 35.62/35.85      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 35.62/35.85  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 35.62/35.85  thf(zf_stmt_4, axiom,
% 35.62/35.85    (![B:$i,A:$i]:
% 35.62/35.85     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 35.62/35.85       ( zip_tseitin_0 @ B @ A ) ))).
% 35.62/35.85  thf(zf_stmt_5, axiom,
% 35.62/35.85    (![A:$i,B:$i,C:$i]:
% 35.62/35.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 35.62/35.85       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 35.62/35.85         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 35.62/35.85           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 35.62/35.85             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 35.62/35.85  thf('105', plain,
% 35.62/35.85      (![X29 : $i, X30 : $i, X31 : $i]:
% 35.62/35.85         (~ (zip_tseitin_0 @ X29 @ X30)
% 35.62/35.85          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 35.62/35.85          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_5])).
% 35.62/35.85  thf('106', plain,
% 35.62/35.85      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A)
% 35.62/35.85        | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 35.62/35.85      inference('sup-', [status(thm)], ['104', '105'])).
% 35.62/35.85  thf('107', plain,
% 35.62/35.85      (![X24 : $i, X25 : $i]:
% 35.62/35.85         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_4])).
% 35.62/35.85  thf('108', plain,
% 35.62/35.85      (![X24 : $i, X25 : $i]:
% 35.62/35.85         ((zip_tseitin_0 @ X24 @ X25) | ((X25) != (k1_xboole_0)))),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_4])).
% 35.62/35.85  thf('109', plain, (![X24 : $i]: (zip_tseitin_0 @ X24 @ k1_xboole_0)),
% 35.62/35.85      inference('simplify', [status(thm)], ['108'])).
% 35.62/35.85  thf('110', plain,
% 35.62/35.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.62/35.85         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 35.62/35.85      inference('sup+', [status(thm)], ['107', '109'])).
% 35.62/35.85  thf('111', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 35.62/35.85      inference('eq_fact', [status(thm)], ['110'])).
% 35.62/35.85  thf('112', plain, ((zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A)),
% 35.62/35.85      inference('demod', [status(thm)], ['106', '111'])).
% 35.62/35.85  thf('113', plain, (((sk_A) = (k1_relat_1 @ sk_B_1))),
% 35.62/35.85      inference('demod', [status(thm)], ['103', '112'])).
% 35.62/35.85  thf('114', plain,
% 35.62/35.85      (![X7 : $i]:
% 35.62/35.85         (~ (v2_funct_1 @ X7)
% 35.62/35.85          | ((k5_relat_1 @ X7 @ (k2_funct_1 @ X7))
% 35.62/35.85              = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 35.62/35.85          | ~ (v1_funct_1 @ X7)
% 35.62/35.85          | ~ (v1_relat_1 @ X7))),
% 35.62/35.85      inference('cnf', [status(esa)], [t61_funct_1])).
% 35.62/35.85  thf('115', plain,
% 35.62/35.85      (![X37 : $i]:
% 35.62/35.85         (m1_subset_1 @ (k6_relat_1 @ X37) @ 
% 35.62/35.85          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 35.62/35.85      inference('demod', [status(thm)], ['59', '60'])).
% 35.62/35.85  thf('116', plain,
% 35.62/35.85      (![X0 : $i]:
% 35.62/35.85         ((m1_subset_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 35.62/35.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 35.62/35.85          | ~ (v1_relat_1 @ X0)
% 35.62/35.85          | ~ (v1_funct_1 @ X0)
% 35.62/35.85          | ~ (v2_funct_1 @ X0))),
% 35.62/35.85      inference('sup+', [status(thm)], ['114', '115'])).
% 35.62/35.85  thf('117', plain,
% 35.62/35.85      (((m1_subset_1 @ (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) @ 
% 35.62/35.85         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_B_1))))
% 35.62/35.85        | ~ (v2_funct_1 @ sk_B_1)
% 35.62/35.85        | ~ (v1_funct_1 @ sk_B_1)
% 35.62/35.85        | ~ (v1_relat_1 @ sk_B_1))),
% 35.62/35.85      inference('sup+', [status(thm)], ['113', '116'])).
% 35.62/35.85  thf('118', plain, (((sk_A) = (k1_relat_1 @ sk_B_1))),
% 35.62/35.85      inference('demod', [status(thm)], ['103', '112'])).
% 35.62/35.85  thf('119', plain, ((v2_funct_1 @ sk_B_1)),
% 35.62/35.85      inference('demod', [status(thm)], ['67', '68', '69'])).
% 35.62/35.85  thf('120', plain, ((v1_funct_1 @ sk_B_1)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('121', plain, ((v1_relat_1 @ sk_B_1)),
% 35.62/35.85      inference('sup-', [status(thm)], ['51', '52'])).
% 35.62/35.85  thf('122', plain,
% 35.62/35.85      ((m1_subset_1 @ (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) @ 
% 35.62/35.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 35.62/35.85      inference('demod', [status(thm)], ['117', '118', '119', '120', '121'])).
% 35.62/35.85  thf('123', plain,
% 35.62/35.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.62/35.85         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 35.62/35.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 35.62/35.85      inference('condensation', [status(thm)], ['74'])).
% 35.62/35.85  thf('124', plain,
% 35.62/35.85      ((r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85        (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) @ 
% 35.62/35.85        (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)))),
% 35.62/35.85      inference('sup-', [status(thm)], ['122', '123'])).
% 35.62/35.85  thf('125', plain,
% 35.62/35.85      (((r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85         (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) @ 
% 35.62/35.85         (k6_relat_1 @ (k1_relat_1 @ sk_B_1)))
% 35.62/35.85        | ~ (v1_relat_1 @ sk_B_1)
% 35.62/35.85        | ~ (v1_funct_1 @ sk_B_1)
% 35.62/35.85        | ~ (v2_funct_1 @ sk_B_1))),
% 35.62/35.85      inference('sup+', [status(thm)], ['96', '124'])).
% 35.62/35.85  thf('126', plain, (((sk_A) = (k1_relat_1 @ sk_B_1))),
% 35.62/35.85      inference('demod', [status(thm)], ['103', '112'])).
% 35.62/35.85  thf('127', plain, ((v1_relat_1 @ sk_B_1)),
% 35.62/35.85      inference('sup-', [status(thm)], ['51', '52'])).
% 35.62/35.85  thf('128', plain, ((v1_funct_1 @ sk_B_1)),
% 35.62/35.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.62/35.85  thf('129', plain, ((v2_funct_1 @ sk_B_1)),
% 35.62/35.85      inference('demod', [status(thm)], ['67', '68', '69'])).
% 35.62/35.85  thf('130', plain,
% 35.62/35.85      ((r2_relset_1 @ sk_A @ sk_A @ 
% 35.62/35.85        (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) @ (k6_relat_1 @ sk_A))),
% 35.62/35.85      inference('demod', [status(thm)], ['125', '126', '127', '128', '129'])).
% 35.62/35.85  thf('131', plain, ($false),
% 35.62/35.85      inference('demod', [status(thm)], ['86', '95', '130'])).
% 35.62/35.85  
% 35.62/35.85  % SZS output end Refutation
% 35.62/35.85  
% 35.62/35.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
