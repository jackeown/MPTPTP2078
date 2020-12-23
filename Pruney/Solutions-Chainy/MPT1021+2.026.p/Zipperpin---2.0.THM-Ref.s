%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8c5oRk7gsf

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:14 EST 2020

% Result     : Theorem 17.06s
% Output     : Refutation 17.06s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 594 expanded)
%              Number of leaves         :   47 ( 200 expanded)
%              Depth                    :   16
%              Number of atoms          : 1791 (11881 expanded)
%              Number of equality atoms :   73 ( 166 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k2_funct_2 @ X46 @ X45 )
        = ( k2_funct_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) )
      | ~ ( v3_funct_2 @ X45 @ X46 @ X46 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X46 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('4',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( v3_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('17',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( v3_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('32',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('34',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('35',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
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

thf('37',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('38',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('41',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
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

thf('44',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('45',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('47',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X28 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('48',plain,(
    ! [X27: $i] :
      ( zip_tseitin_0 @ X27 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['49'])).

thf('51',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('54',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('55',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('57',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_partfun1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,
    ( ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['52','59'])).

thf('61',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['42','51'])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v3_funct_2 @ X24 @ X25 @ X26 )
      | ( v2_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('64',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('70',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('71',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r1_tarski @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','67','68','71'])).

thf('73',plain,(
    ! [X1: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('74',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('76',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','78'])).

thf('80',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['42','51'])).

thf('81',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('82',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 )
      | ( X19 != X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('83',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['69','70'])).

thf('86',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('88',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80','84','85','86','87'])).

thf('89',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','32','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('91',plain,
    ( $false
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','8','89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('94',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('99',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('104',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('105',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v3_funct_2 @ X24 @ X25 @ X26 )
      | ( v2_funct_2 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('108',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['108','109','110'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('112',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v2_funct_2 @ X36 @ X35 )
      | ( ( k2_relat_1 @ X36 )
        = X35 )
      | ~ ( v5_relat_1 @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('113',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['69','70'])).

thf('115',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('116',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('117',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['113','114','117'])).

thf('119',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('120',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['118','121'])).

thf('123',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['113','114','117'])).

thf('124',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('125',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['69','70'])).

thf('127',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('129',plain,
    ( ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['105','129'])).

thf('131',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['113','114','117'])).

thf('132',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('133',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['69','70'])).

thf('134',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('136',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['130','131','132','133','134','135'])).

thf('137',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['101','102','136'])).

thf('138',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('139',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('140',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('143',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('145',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['143','144'])).

thf('146',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['91','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8c5oRk7gsf
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:32:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 17.06/17.31  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.06/17.31  % Solved by: fo/fo7.sh
% 17.06/17.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.06/17.31  % done 3118 iterations in 16.852s
% 17.06/17.31  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.06/17.31  % SZS output start Refutation
% 17.06/17.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 17.06/17.31  thf(sk_A_type, type, sk_A: $i).
% 17.06/17.31  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 17.06/17.31  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 17.06/17.31  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 17.06/17.31  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 17.06/17.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 17.06/17.31  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 17.06/17.31  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 17.06/17.31  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 17.06/17.31  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 17.06/17.31  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 17.06/17.31  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 17.06/17.31  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 17.06/17.31  thf(sk_B_type, type, sk_B: $i).
% 17.06/17.31  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 17.06/17.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 17.06/17.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.06/17.31  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 17.06/17.31  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 17.06/17.31  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 17.06/17.31  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 17.06/17.31  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 17.06/17.31  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 17.06/17.31  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 17.06/17.31  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 17.06/17.31  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 17.06/17.31  thf(t88_funct_2, conjecture,
% 17.06/17.31    (![A:$i,B:$i]:
% 17.06/17.31     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 17.06/17.31         ( v3_funct_2 @ B @ A @ A ) & 
% 17.06/17.31         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 17.06/17.31       ( ( r2_relset_1 @
% 17.06/17.31           A @ A @ 
% 17.06/17.31           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 17.06/17.31           ( k6_partfun1 @ A ) ) & 
% 17.06/17.31         ( r2_relset_1 @
% 17.06/17.31           A @ A @ 
% 17.06/17.31           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 17.06/17.31           ( k6_partfun1 @ A ) ) ) ))).
% 17.06/17.31  thf(zf_stmt_0, negated_conjecture,
% 17.06/17.31    (~( ![A:$i,B:$i]:
% 17.06/17.31        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 17.06/17.31            ( v3_funct_2 @ B @ A @ A ) & 
% 17.06/17.31            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 17.06/17.31          ( ( r2_relset_1 @
% 17.06/17.31              A @ A @ 
% 17.06/17.31              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 17.06/17.31              ( k6_partfun1 @ A ) ) & 
% 17.06/17.31            ( r2_relset_1 @
% 17.06/17.31              A @ A @ 
% 17.06/17.31              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 17.06/17.31              ( k6_partfun1 @ A ) ) ) ) )),
% 17.06/17.31    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 17.06/17.31  thf('0', plain,
% 17.06/17.31      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 17.06/17.31           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 17.06/17.31            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 17.06/17.31           (k6_partfun1 @ sk_A))
% 17.06/17.31        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 17.06/17.31             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 17.06/17.31              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 17.06/17.31             (k6_partfun1 @ sk_A)))),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('1', plain,
% 17.06/17.31      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 17.06/17.31           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 17.06/17.31            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 17.06/17.31           (k6_partfun1 @ sk_A)))
% 17.06/17.31         <= (~
% 17.06/17.31             ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.06/17.31               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 17.06/17.31                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 17.06/17.31               (k6_partfun1 @ sk_A))))),
% 17.06/17.31      inference('split', [status(esa)], ['0'])).
% 17.06/17.31  thf('2', plain,
% 17.06/17.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf(redefinition_k2_funct_2, axiom,
% 17.06/17.31    (![A:$i,B:$i]:
% 17.06/17.31     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 17.06/17.31         ( v3_funct_2 @ B @ A @ A ) & 
% 17.06/17.31         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 17.06/17.31       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 17.06/17.31  thf('3', plain,
% 17.06/17.31      (![X45 : $i, X46 : $i]:
% 17.06/17.31         (((k2_funct_2 @ X46 @ X45) = (k2_funct_1 @ X45))
% 17.06/17.31          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X46)))
% 17.06/17.31          | ~ (v3_funct_2 @ X45 @ X46 @ X46)
% 17.06/17.31          | ~ (v1_funct_2 @ X45 @ X46 @ X46)
% 17.06/17.31          | ~ (v1_funct_1 @ X45))),
% 17.06/17.31      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 17.06/17.31  thf('4', plain,
% 17.06/17.31      ((~ (v1_funct_1 @ sk_B)
% 17.06/17.31        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 17.06/17.31        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 17.06/17.31        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 17.06/17.31      inference('sup-', [status(thm)], ['2', '3'])).
% 17.06/17.31  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('6', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('7', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('8', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 17.06/17.31      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 17.06/17.31  thf('9', plain,
% 17.06/17.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf(dt_k2_funct_2, axiom,
% 17.06/17.31    (![A:$i,B:$i]:
% 17.06/17.31     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 17.06/17.31         ( v3_funct_2 @ B @ A @ A ) & 
% 17.06/17.31         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 17.06/17.31       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 17.06/17.31         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 17.06/17.31         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 17.06/17.31         ( m1_subset_1 @
% 17.06/17.31           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 17.06/17.31  thf('10', plain,
% 17.06/17.31      (![X37 : $i, X38 : $i]:
% 17.06/17.31         ((m1_subset_1 @ (k2_funct_2 @ X37 @ X38) @ 
% 17.06/17.31           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 17.06/17.31          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 17.06/17.31          | ~ (v3_funct_2 @ X38 @ X37 @ X37)
% 17.06/17.31          | ~ (v1_funct_2 @ X38 @ X37 @ X37)
% 17.06/17.31          | ~ (v1_funct_1 @ X38))),
% 17.06/17.31      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 17.06/17.31  thf('11', plain,
% 17.06/17.31      ((~ (v1_funct_1 @ sk_B)
% 17.06/17.31        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 17.06/17.31        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 17.06/17.31        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 17.06/17.31           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 17.06/17.31      inference('sup-', [status(thm)], ['9', '10'])).
% 17.06/17.31  thf('12', plain, ((v1_funct_1 @ sk_B)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('13', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('14', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('15', plain,
% 17.06/17.31      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 17.06/17.31        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.06/17.31      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 17.06/17.31  thf('16', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 17.06/17.31      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 17.06/17.31  thf('17', plain,
% 17.06/17.31      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 17.06/17.31        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.06/17.31      inference('demod', [status(thm)], ['15', '16'])).
% 17.06/17.31  thf('18', plain,
% 17.06/17.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf(redefinition_k1_partfun1, axiom,
% 17.06/17.31    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 17.06/17.31     ( ( ( v1_funct_1 @ E ) & 
% 17.06/17.31         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 17.06/17.31         ( v1_funct_1 @ F ) & 
% 17.06/17.31         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 17.06/17.31       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 17.06/17.31  thf('19', plain,
% 17.06/17.31      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 17.06/17.31         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 17.06/17.31          | ~ (v1_funct_1 @ X39)
% 17.06/17.31          | ~ (v1_funct_1 @ X42)
% 17.06/17.31          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 17.06/17.31          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 17.06/17.31              = (k5_relat_1 @ X39 @ X42)))),
% 17.06/17.31      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 17.06/17.31  thf('20', plain,
% 17.06/17.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.06/17.31         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 17.06/17.31            = (k5_relat_1 @ sk_B @ X0))
% 17.06/17.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 17.06/17.31          | ~ (v1_funct_1 @ X0)
% 17.06/17.31          | ~ (v1_funct_1 @ sk_B))),
% 17.06/17.31      inference('sup-', [status(thm)], ['18', '19'])).
% 17.06/17.31  thf('21', plain, ((v1_funct_1 @ sk_B)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('22', plain,
% 17.06/17.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.06/17.31         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 17.06/17.31            = (k5_relat_1 @ sk_B @ X0))
% 17.06/17.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 17.06/17.31          | ~ (v1_funct_1 @ X0))),
% 17.06/17.31      inference('demod', [status(thm)], ['20', '21'])).
% 17.06/17.31  thf('23', plain,
% 17.06/17.31      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 17.06/17.31        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 17.06/17.31            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 17.06/17.31      inference('sup-', [status(thm)], ['17', '22'])).
% 17.06/17.31  thf('24', plain,
% 17.06/17.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('25', plain,
% 17.06/17.31      (![X37 : $i, X38 : $i]:
% 17.06/17.31         ((v1_funct_1 @ (k2_funct_2 @ X37 @ X38))
% 17.06/17.31          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 17.06/17.31          | ~ (v3_funct_2 @ X38 @ X37 @ X37)
% 17.06/17.31          | ~ (v1_funct_2 @ X38 @ X37 @ X37)
% 17.06/17.31          | ~ (v1_funct_1 @ X38))),
% 17.06/17.31      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 17.06/17.31  thf('26', plain,
% 17.06/17.31      ((~ (v1_funct_1 @ sk_B)
% 17.06/17.31        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 17.06/17.31        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 17.06/17.31        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 17.06/17.31      inference('sup-', [status(thm)], ['24', '25'])).
% 17.06/17.31  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('28', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('29', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('30', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 17.06/17.31      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 17.06/17.31  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 17.06/17.31      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 17.06/17.31  thf('32', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 17.06/17.31      inference('demod', [status(thm)], ['30', '31'])).
% 17.06/17.31  thf(t61_funct_1, axiom,
% 17.06/17.31    (![A:$i]:
% 17.06/17.31     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 17.06/17.31       ( ( v2_funct_1 @ A ) =>
% 17.06/17.31         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 17.06/17.31             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 17.06/17.31           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 17.06/17.31             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 17.06/17.31  thf('33', plain,
% 17.06/17.31      (![X9 : $i]:
% 17.06/17.31         (~ (v2_funct_1 @ X9)
% 17.06/17.31          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 17.06/17.31              = (k6_relat_1 @ (k1_relat_1 @ X9)))
% 17.06/17.31          | ~ (v1_funct_1 @ X9)
% 17.06/17.31          | ~ (v1_relat_1 @ X9))),
% 17.06/17.31      inference('cnf', [status(esa)], [t61_funct_1])).
% 17.06/17.31  thf(redefinition_k6_partfun1, axiom,
% 17.06/17.31    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 17.06/17.31  thf('34', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 17.06/17.31      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 17.06/17.31  thf('35', plain,
% 17.06/17.31      (![X9 : $i]:
% 17.06/17.31         (~ (v2_funct_1 @ X9)
% 17.06/17.31          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 17.06/17.31              = (k6_partfun1 @ (k1_relat_1 @ X9)))
% 17.06/17.31          | ~ (v1_funct_1 @ X9)
% 17.06/17.31          | ~ (v1_relat_1 @ X9))),
% 17.06/17.31      inference('demod', [status(thm)], ['33', '34'])).
% 17.06/17.31  thf('36', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf(d1_funct_2, axiom,
% 17.06/17.31    (![A:$i,B:$i,C:$i]:
% 17.06/17.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.06/17.31       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 17.06/17.31           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 17.06/17.31             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 17.06/17.31         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 17.06/17.31           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 17.06/17.31             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 17.06/17.31  thf(zf_stmt_1, axiom,
% 17.06/17.31    (![C:$i,B:$i,A:$i]:
% 17.06/17.31     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 17.06/17.31       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 17.06/17.31  thf('37', plain,
% 17.06/17.31      (![X29 : $i, X30 : $i, X31 : $i]:
% 17.06/17.31         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 17.06/17.31          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 17.06/17.31          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_1])).
% 17.06/17.31  thf('38', plain,
% 17.06/17.31      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 17.06/17.31        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 17.06/17.31      inference('sup-', [status(thm)], ['36', '37'])).
% 17.06/17.31  thf('39', plain,
% 17.06/17.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf(redefinition_k1_relset_1, axiom,
% 17.06/17.31    (![A:$i,B:$i,C:$i]:
% 17.06/17.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.06/17.31       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 17.06/17.31  thf('40', plain,
% 17.06/17.31      (![X16 : $i, X17 : $i, X18 : $i]:
% 17.06/17.31         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 17.06/17.31          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 17.06/17.31      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 17.06/17.31  thf('41', plain,
% 17.06/17.31      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 17.06/17.31      inference('sup-', [status(thm)], ['39', '40'])).
% 17.06/17.31  thf('42', plain,
% 17.06/17.31      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_B)))),
% 17.06/17.31      inference('demod', [status(thm)], ['38', '41'])).
% 17.06/17.31  thf('43', plain,
% 17.06/17.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 17.06/17.31  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 17.06/17.31  thf(zf_stmt_4, axiom,
% 17.06/17.31    (![B:$i,A:$i]:
% 17.06/17.31     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 17.06/17.31       ( zip_tseitin_0 @ B @ A ) ))).
% 17.06/17.31  thf(zf_stmt_5, axiom,
% 17.06/17.31    (![A:$i,B:$i,C:$i]:
% 17.06/17.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.06/17.31       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 17.06/17.31         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 17.06/17.31           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 17.06/17.31             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 17.06/17.31  thf('44', plain,
% 17.06/17.31      (![X32 : $i, X33 : $i, X34 : $i]:
% 17.06/17.31         (~ (zip_tseitin_0 @ X32 @ X33)
% 17.06/17.31          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 17.06/17.31          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_5])).
% 17.06/17.31  thf('45', plain,
% 17.06/17.31      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 17.06/17.31      inference('sup-', [status(thm)], ['43', '44'])).
% 17.06/17.31  thf('46', plain,
% 17.06/17.31      (![X27 : $i, X28 : $i]:
% 17.06/17.31         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_4])).
% 17.06/17.31  thf('47', plain,
% 17.06/17.31      (![X27 : $i, X28 : $i]:
% 17.06/17.31         ((zip_tseitin_0 @ X27 @ X28) | ((X28) != (k1_xboole_0)))),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_4])).
% 17.06/17.31  thf('48', plain, (![X27 : $i]: (zip_tseitin_0 @ X27 @ k1_xboole_0)),
% 17.06/17.31      inference('simplify', [status(thm)], ['47'])).
% 17.06/17.31  thf('49', plain,
% 17.06/17.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.06/17.31         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 17.06/17.31      inference('sup+', [status(thm)], ['46', '48'])).
% 17.06/17.31  thf('50', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 17.06/17.31      inference('eq_fact', [status(thm)], ['49'])).
% 17.06/17.31  thf('51', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 17.06/17.31      inference('demod', [status(thm)], ['45', '50'])).
% 17.06/17.31  thf('52', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 17.06/17.31      inference('demod', [status(thm)], ['42', '51'])).
% 17.06/17.31  thf('53', plain,
% 17.06/17.31      (![X9 : $i]:
% 17.06/17.31         (~ (v2_funct_1 @ X9)
% 17.06/17.31          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 17.06/17.31              = (k6_partfun1 @ (k1_relat_1 @ X9)))
% 17.06/17.31          | ~ (v1_funct_1 @ X9)
% 17.06/17.31          | ~ (v1_relat_1 @ X9))),
% 17.06/17.31      inference('demod', [status(thm)], ['33', '34'])).
% 17.06/17.31  thf(t29_relset_1, axiom,
% 17.06/17.31    (![A:$i]:
% 17.06/17.31     ( m1_subset_1 @
% 17.06/17.31       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 17.06/17.31  thf('54', plain,
% 17.06/17.31      (![X23 : $i]:
% 17.06/17.31         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 17.06/17.31          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 17.06/17.31      inference('cnf', [status(esa)], [t29_relset_1])).
% 17.06/17.31  thf('55', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 17.06/17.31      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 17.06/17.31  thf('56', plain,
% 17.06/17.31      (![X23 : $i]:
% 17.06/17.31         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 17.06/17.31          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 17.06/17.31      inference('demod', [status(thm)], ['54', '55'])).
% 17.06/17.31  thf(t3_subset, axiom,
% 17.06/17.31    (![A:$i,B:$i]:
% 17.06/17.31     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 17.06/17.31  thf('57', plain,
% 17.06/17.31      (![X1 : $i, X2 : $i]:
% 17.06/17.31         ((r1_tarski @ X1 @ X2) | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 17.06/17.31      inference('cnf', [status(esa)], [t3_subset])).
% 17.06/17.31  thf('58', plain,
% 17.06/17.31      (![X0 : $i]: (r1_tarski @ (k6_partfun1 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 17.06/17.31      inference('sup-', [status(thm)], ['56', '57'])).
% 17.06/17.31  thf('59', plain,
% 17.06/17.31      (![X0 : $i]:
% 17.06/17.31         ((r1_tarski @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 17.06/17.31           (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 17.06/17.31          | ~ (v1_relat_1 @ X0)
% 17.06/17.31          | ~ (v1_funct_1 @ X0)
% 17.06/17.31          | ~ (v2_funct_1 @ X0))),
% 17.06/17.31      inference('sup+', [status(thm)], ['53', '58'])).
% 17.06/17.31  thf('60', plain,
% 17.06/17.31      (((r1_tarski @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 17.06/17.31         (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 17.06/17.31        | ~ (v2_funct_1 @ sk_B)
% 17.06/17.31        | ~ (v1_funct_1 @ sk_B)
% 17.06/17.31        | ~ (v1_relat_1 @ sk_B))),
% 17.06/17.31      inference('sup+', [status(thm)], ['52', '59'])).
% 17.06/17.31  thf('61', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 17.06/17.31      inference('demod', [status(thm)], ['42', '51'])).
% 17.06/17.31  thf('62', plain,
% 17.06/17.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf(cc2_funct_2, axiom,
% 17.06/17.31    (![A:$i,B:$i,C:$i]:
% 17.06/17.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.06/17.31       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 17.06/17.31         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 17.06/17.31  thf('63', plain,
% 17.06/17.31      (![X24 : $i, X25 : $i, X26 : $i]:
% 17.06/17.31         (~ (v1_funct_1 @ X24)
% 17.06/17.31          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 17.06/17.31          | (v2_funct_1 @ X24)
% 17.06/17.31          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 17.06/17.31      inference('cnf', [status(esa)], [cc2_funct_2])).
% 17.06/17.31  thf('64', plain,
% 17.06/17.31      (((v2_funct_1 @ sk_B)
% 17.06/17.31        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 17.06/17.31        | ~ (v1_funct_1 @ sk_B))),
% 17.06/17.31      inference('sup-', [status(thm)], ['62', '63'])).
% 17.06/17.31  thf('65', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('66', plain, ((v1_funct_1 @ sk_B)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('67', plain, ((v2_funct_1 @ sk_B)),
% 17.06/17.31      inference('demod', [status(thm)], ['64', '65', '66'])).
% 17.06/17.31  thf('68', plain, ((v1_funct_1 @ sk_B)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('69', plain,
% 17.06/17.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf(cc1_relset_1, axiom,
% 17.06/17.31    (![A:$i,B:$i,C:$i]:
% 17.06/17.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.06/17.31       ( v1_relat_1 @ C ) ))).
% 17.06/17.31  thf('70', plain,
% 17.06/17.31      (![X10 : $i, X11 : $i, X12 : $i]:
% 17.06/17.31         ((v1_relat_1 @ X10)
% 17.06/17.31          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 17.06/17.31      inference('cnf', [status(esa)], [cc1_relset_1])).
% 17.06/17.31  thf('71', plain, ((v1_relat_1 @ sk_B)),
% 17.06/17.31      inference('sup-', [status(thm)], ['69', '70'])).
% 17.06/17.31  thf('72', plain,
% 17.06/17.31      ((r1_tarski @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 17.06/17.31        (k2_zfmisc_1 @ sk_A @ sk_A))),
% 17.06/17.31      inference('demod', [status(thm)], ['60', '61', '67', '68', '71'])).
% 17.06/17.31  thf('73', plain,
% 17.06/17.31      (![X1 : $i, X3 : $i]:
% 17.06/17.31         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X1 @ X3))),
% 17.06/17.31      inference('cnf', [status(esa)], [t3_subset])).
% 17.06/17.31  thf('74', plain,
% 17.06/17.31      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 17.06/17.31        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.06/17.31      inference('sup-', [status(thm)], ['72', '73'])).
% 17.06/17.31  thf('75', plain,
% 17.06/17.31      (![X23 : $i]:
% 17.06/17.31         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 17.06/17.31          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 17.06/17.31      inference('demod', [status(thm)], ['54', '55'])).
% 17.06/17.31  thf(redefinition_r2_relset_1, axiom,
% 17.06/17.31    (![A:$i,B:$i,C:$i,D:$i]:
% 17.06/17.31     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 17.06/17.31         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 17.06/17.31       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 17.06/17.31  thf('76', plain,
% 17.06/17.31      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 17.06/17.31         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 17.06/17.31          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 17.06/17.31          | ((X19) = (X22))
% 17.06/17.31          | ~ (r2_relset_1 @ X20 @ X21 @ X19 @ X22))),
% 17.06/17.31      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 17.06/17.31  thf('77', plain,
% 17.06/17.31      (![X0 : $i, X1 : $i]:
% 17.06/17.31         (~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 17.06/17.31          | ((k6_partfun1 @ X0) = (X1))
% 17.06/17.31          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 17.06/17.31      inference('sup-', [status(thm)], ['75', '76'])).
% 17.06/17.31  thf('78', plain,
% 17.06/17.31      ((((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 17.06/17.31        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 17.06/17.31             (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 17.06/17.31      inference('sup-', [status(thm)], ['74', '77'])).
% 17.06/17.31  thf('79', plain,
% 17.06/17.31      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 17.06/17.31           (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 17.06/17.31        | ~ (v1_relat_1 @ sk_B)
% 17.06/17.31        | ~ (v1_funct_1 @ sk_B)
% 17.06/17.31        | ~ (v2_funct_1 @ sk_B)
% 17.06/17.31        | ((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 17.06/17.31      inference('sup-', [status(thm)], ['35', '78'])).
% 17.06/17.31  thf('80', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 17.06/17.31      inference('demod', [status(thm)], ['42', '51'])).
% 17.06/17.31  thf('81', plain,
% 17.06/17.31      (![X23 : $i]:
% 17.06/17.31         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 17.06/17.31          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 17.06/17.31      inference('demod', [status(thm)], ['54', '55'])).
% 17.06/17.31  thf('82', plain,
% 17.06/17.31      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 17.06/17.31         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 17.06/17.31          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 17.06/17.31          | (r2_relset_1 @ X20 @ X21 @ X19 @ X22)
% 17.06/17.31          | ((X19) != (X22)))),
% 17.06/17.31      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 17.06/17.31  thf('83', plain,
% 17.06/17.31      (![X20 : $i, X21 : $i, X22 : $i]:
% 17.06/17.31         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 17.06/17.31          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 17.06/17.31      inference('simplify', [status(thm)], ['82'])).
% 17.06/17.31  thf('84', plain,
% 17.06/17.31      (![X0 : $i]:
% 17.06/17.31         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 17.06/17.31      inference('sup-', [status(thm)], ['81', '83'])).
% 17.06/17.31  thf('85', plain, ((v1_relat_1 @ sk_B)),
% 17.06/17.31      inference('sup-', [status(thm)], ['69', '70'])).
% 17.06/17.31  thf('86', plain, ((v1_funct_1 @ sk_B)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('87', plain, ((v2_funct_1 @ sk_B)),
% 17.06/17.31      inference('demod', [status(thm)], ['64', '65', '66'])).
% 17.06/17.31  thf('88', plain,
% 17.06/17.31      (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 17.06/17.31      inference('demod', [status(thm)], ['79', '80', '84', '85', '86', '87'])).
% 17.06/17.31  thf('89', plain,
% 17.06/17.31      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 17.06/17.31         = (k6_partfun1 @ sk_A))),
% 17.06/17.31      inference('demod', [status(thm)], ['23', '32', '88'])).
% 17.06/17.31  thf('90', plain,
% 17.06/17.31      (![X0 : $i]:
% 17.06/17.31         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 17.06/17.31      inference('sup-', [status(thm)], ['81', '83'])).
% 17.06/17.31  thf('91', plain,
% 17.06/17.31      (($false)
% 17.06/17.31         <= (~
% 17.06/17.31             ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.06/17.31               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 17.06/17.31                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 17.06/17.31               (k6_partfun1 @ sk_A))))),
% 17.06/17.31      inference('demod', [status(thm)], ['1', '8', '89', '90'])).
% 17.06/17.31  thf('92', plain,
% 17.06/17.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('93', plain,
% 17.06/17.31      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 17.06/17.31        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.06/17.31      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 17.06/17.31  thf('94', plain,
% 17.06/17.31      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 17.06/17.31         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 17.06/17.31          | ~ (v1_funct_1 @ X39)
% 17.06/17.31          | ~ (v1_funct_1 @ X42)
% 17.06/17.31          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 17.06/17.31          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 17.06/17.31              = (k5_relat_1 @ X39 @ X42)))),
% 17.06/17.31      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 17.06/17.31  thf('95', plain,
% 17.06/17.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.06/17.31         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 17.06/17.31            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 17.06/17.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 17.06/17.31          | ~ (v1_funct_1 @ X0)
% 17.06/17.31          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 17.06/17.31      inference('sup-', [status(thm)], ['93', '94'])).
% 17.06/17.31  thf('96', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 17.06/17.31      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 17.06/17.31  thf('97', plain,
% 17.06/17.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.06/17.31         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 17.06/17.31            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 17.06/17.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 17.06/17.31          | ~ (v1_funct_1 @ X0))),
% 17.06/17.31      inference('demod', [status(thm)], ['95', '96'])).
% 17.06/17.31  thf('98', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 17.06/17.31      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 17.06/17.31  thf('99', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 17.06/17.31      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 17.06/17.31  thf('100', plain,
% 17.06/17.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.06/17.31         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 17.06/17.31            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 17.06/17.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 17.06/17.31          | ~ (v1_funct_1 @ X0))),
% 17.06/17.31      inference('demod', [status(thm)], ['97', '98', '99'])).
% 17.06/17.31  thf('101', plain,
% 17.06/17.31      ((~ (v1_funct_1 @ sk_B)
% 17.06/17.31        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 17.06/17.31            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 17.06/17.31      inference('sup-', [status(thm)], ['92', '100'])).
% 17.06/17.31  thf('102', plain, ((v1_funct_1 @ sk_B)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('103', plain,
% 17.06/17.31      (![X9 : $i]:
% 17.06/17.31         (~ (v2_funct_1 @ X9)
% 17.06/17.31          | ((k5_relat_1 @ (k2_funct_1 @ X9) @ X9)
% 17.06/17.31              = (k6_relat_1 @ (k2_relat_1 @ X9)))
% 17.06/17.31          | ~ (v1_funct_1 @ X9)
% 17.06/17.31          | ~ (v1_relat_1 @ X9))),
% 17.06/17.31      inference('cnf', [status(esa)], [t61_funct_1])).
% 17.06/17.31  thf('104', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 17.06/17.31      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 17.06/17.31  thf('105', plain,
% 17.06/17.31      (![X9 : $i]:
% 17.06/17.31         (~ (v2_funct_1 @ X9)
% 17.06/17.31          | ((k5_relat_1 @ (k2_funct_1 @ X9) @ X9)
% 17.06/17.31              = (k6_partfun1 @ (k2_relat_1 @ X9)))
% 17.06/17.31          | ~ (v1_funct_1 @ X9)
% 17.06/17.31          | ~ (v1_relat_1 @ X9))),
% 17.06/17.31      inference('demod', [status(thm)], ['103', '104'])).
% 17.06/17.31  thf('106', plain,
% 17.06/17.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('107', plain,
% 17.06/17.31      (![X24 : $i, X25 : $i, X26 : $i]:
% 17.06/17.31         (~ (v1_funct_1 @ X24)
% 17.06/17.31          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 17.06/17.31          | (v2_funct_2 @ X24 @ X26)
% 17.06/17.31          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 17.06/17.31      inference('cnf', [status(esa)], [cc2_funct_2])).
% 17.06/17.31  thf('108', plain,
% 17.06/17.31      (((v2_funct_2 @ sk_B @ sk_A)
% 17.06/17.31        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 17.06/17.31        | ~ (v1_funct_1 @ sk_B))),
% 17.06/17.31      inference('sup-', [status(thm)], ['106', '107'])).
% 17.06/17.31  thf('109', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('110', plain, ((v1_funct_1 @ sk_B)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('111', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 17.06/17.31      inference('demod', [status(thm)], ['108', '109', '110'])).
% 17.06/17.31  thf(d3_funct_2, axiom,
% 17.06/17.31    (![A:$i,B:$i]:
% 17.06/17.31     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 17.06/17.31       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 17.06/17.31  thf('112', plain,
% 17.06/17.31      (![X35 : $i, X36 : $i]:
% 17.06/17.31         (~ (v2_funct_2 @ X36 @ X35)
% 17.06/17.31          | ((k2_relat_1 @ X36) = (X35))
% 17.06/17.31          | ~ (v5_relat_1 @ X36 @ X35)
% 17.06/17.31          | ~ (v1_relat_1 @ X36))),
% 17.06/17.31      inference('cnf', [status(esa)], [d3_funct_2])).
% 17.06/17.31  thf('113', plain,
% 17.06/17.31      ((~ (v1_relat_1 @ sk_B)
% 17.06/17.31        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 17.06/17.31        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 17.06/17.31      inference('sup-', [status(thm)], ['111', '112'])).
% 17.06/17.31  thf('114', plain, ((v1_relat_1 @ sk_B)),
% 17.06/17.31      inference('sup-', [status(thm)], ['69', '70'])).
% 17.06/17.31  thf('115', plain,
% 17.06/17.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf(cc2_relset_1, axiom,
% 17.06/17.31    (![A:$i,B:$i,C:$i]:
% 17.06/17.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.06/17.31       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 17.06/17.31  thf('116', plain,
% 17.06/17.31      (![X13 : $i, X14 : $i, X15 : $i]:
% 17.06/17.31         ((v5_relat_1 @ X13 @ X15)
% 17.06/17.31          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 17.06/17.31      inference('cnf', [status(esa)], [cc2_relset_1])).
% 17.06/17.31  thf('117', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 17.06/17.31      inference('sup-', [status(thm)], ['115', '116'])).
% 17.06/17.31  thf('118', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 17.06/17.31      inference('demod', [status(thm)], ['113', '114', '117'])).
% 17.06/17.31  thf('119', plain,
% 17.06/17.31      (![X9 : $i]:
% 17.06/17.31         (~ (v2_funct_1 @ X9)
% 17.06/17.31          | ((k5_relat_1 @ (k2_funct_1 @ X9) @ X9)
% 17.06/17.31              = (k6_partfun1 @ (k2_relat_1 @ X9)))
% 17.06/17.31          | ~ (v1_funct_1 @ X9)
% 17.06/17.31          | ~ (v1_relat_1 @ X9))),
% 17.06/17.31      inference('demod', [status(thm)], ['103', '104'])).
% 17.06/17.31  thf('120', plain,
% 17.06/17.31      (![X23 : $i]:
% 17.06/17.31         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 17.06/17.31          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 17.06/17.31      inference('demod', [status(thm)], ['54', '55'])).
% 17.06/17.31  thf('121', plain,
% 17.06/17.31      (![X0 : $i]:
% 17.06/17.31         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 17.06/17.31           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 17.06/17.31          | ~ (v1_relat_1 @ X0)
% 17.06/17.31          | ~ (v1_funct_1 @ X0)
% 17.06/17.31          | ~ (v2_funct_1 @ X0))),
% 17.06/17.31      inference('sup+', [status(thm)], ['119', '120'])).
% 17.06/17.31  thf('122', plain,
% 17.06/17.31      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 17.06/17.31         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 17.06/17.31        | ~ (v2_funct_1 @ sk_B)
% 17.06/17.31        | ~ (v1_funct_1 @ sk_B)
% 17.06/17.31        | ~ (v1_relat_1 @ sk_B))),
% 17.06/17.31      inference('sup+', [status(thm)], ['118', '121'])).
% 17.06/17.31  thf('123', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 17.06/17.31      inference('demod', [status(thm)], ['113', '114', '117'])).
% 17.06/17.31  thf('124', plain, ((v2_funct_1 @ sk_B)),
% 17.06/17.31      inference('demod', [status(thm)], ['64', '65', '66'])).
% 17.06/17.31  thf('125', plain, ((v1_funct_1 @ sk_B)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('126', plain, ((v1_relat_1 @ sk_B)),
% 17.06/17.31      inference('sup-', [status(thm)], ['69', '70'])).
% 17.06/17.31  thf('127', plain,
% 17.06/17.31      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 17.06/17.31        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 17.06/17.31      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 17.06/17.31  thf('128', plain,
% 17.06/17.31      (![X0 : $i, X1 : $i]:
% 17.06/17.31         (~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 17.06/17.31          | ((k6_partfun1 @ X0) = (X1))
% 17.06/17.31          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 17.06/17.31      inference('sup-', [status(thm)], ['75', '76'])).
% 17.06/17.31  thf('129', plain,
% 17.06/17.31      ((((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 17.06/17.31        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 17.06/17.31             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 17.06/17.31      inference('sup-', [status(thm)], ['127', '128'])).
% 17.06/17.31  thf('130', plain,
% 17.06/17.31      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 17.06/17.31           (k6_partfun1 @ (k2_relat_1 @ sk_B)))
% 17.06/17.31        | ~ (v1_relat_1 @ sk_B)
% 17.06/17.31        | ~ (v1_funct_1 @ sk_B)
% 17.06/17.31        | ~ (v2_funct_1 @ sk_B)
% 17.06/17.31        | ((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 17.06/17.31      inference('sup-', [status(thm)], ['105', '129'])).
% 17.06/17.31  thf('131', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 17.06/17.31      inference('demod', [status(thm)], ['113', '114', '117'])).
% 17.06/17.31  thf('132', plain,
% 17.06/17.31      (![X0 : $i]:
% 17.06/17.31         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 17.06/17.31      inference('sup-', [status(thm)], ['81', '83'])).
% 17.06/17.31  thf('133', plain, ((v1_relat_1 @ sk_B)),
% 17.06/17.31      inference('sup-', [status(thm)], ['69', '70'])).
% 17.06/17.31  thf('134', plain, ((v1_funct_1 @ sk_B)),
% 17.06/17.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.06/17.31  thf('135', plain, ((v2_funct_1 @ sk_B)),
% 17.06/17.31      inference('demod', [status(thm)], ['64', '65', '66'])).
% 17.06/17.31  thf('136', plain,
% 17.06/17.31      (((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 17.06/17.31      inference('demod', [status(thm)],
% 17.06/17.31                ['130', '131', '132', '133', '134', '135'])).
% 17.06/17.31  thf('137', plain,
% 17.06/17.31      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 17.06/17.31         = (k6_partfun1 @ sk_A))),
% 17.06/17.31      inference('demod', [status(thm)], ['101', '102', '136'])).
% 17.06/17.31  thf('138', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 17.06/17.31      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 17.06/17.31  thf('139', plain,
% 17.06/17.31      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 17.06/17.31           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 17.06/17.31            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 17.06/17.31           (k6_partfun1 @ sk_A)))
% 17.06/17.31         <= (~
% 17.06/17.31             ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.06/17.31               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 17.06/17.31                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 17.06/17.31               (k6_partfun1 @ sk_A))))),
% 17.06/17.31      inference('split', [status(esa)], ['0'])).
% 17.06/17.31  thf('140', plain,
% 17.06/17.31      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 17.06/17.31           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 17.06/17.31            sk_B) @ 
% 17.06/17.31           (k6_partfun1 @ sk_A)))
% 17.06/17.31         <= (~
% 17.06/17.31             ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.06/17.31               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 17.06/17.31                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 17.06/17.31               (k6_partfun1 @ sk_A))))),
% 17.06/17.31      inference('sup-', [status(thm)], ['138', '139'])).
% 17.06/17.31  thf('141', plain,
% 17.06/17.31      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 17.06/17.31           (k6_partfun1 @ sk_A)))
% 17.06/17.31         <= (~
% 17.06/17.31             ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.06/17.31               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 17.06/17.31                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 17.06/17.31               (k6_partfun1 @ sk_A))))),
% 17.06/17.31      inference('sup-', [status(thm)], ['137', '140'])).
% 17.06/17.31  thf('142', plain,
% 17.06/17.31      (![X0 : $i]:
% 17.06/17.31         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 17.06/17.31      inference('sup-', [status(thm)], ['81', '83'])).
% 17.06/17.31  thf('143', plain,
% 17.06/17.31      (((r2_relset_1 @ sk_A @ sk_A @ 
% 17.06/17.31         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 17.06/17.31          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 17.06/17.31         (k6_partfun1 @ sk_A)))),
% 17.06/17.31      inference('demod', [status(thm)], ['141', '142'])).
% 17.06/17.31  thf('144', plain,
% 17.06/17.31      (~
% 17.06/17.31       ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.06/17.31         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 17.06/17.31          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 17.06/17.31         (k6_partfun1 @ sk_A))) | 
% 17.06/17.31       ~
% 17.06/17.31       ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.06/17.31         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 17.06/17.31          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 17.06/17.31         (k6_partfun1 @ sk_A)))),
% 17.06/17.31      inference('split', [status(esa)], ['0'])).
% 17.06/17.31  thf('145', plain,
% 17.06/17.31      (~
% 17.06/17.31       ((r2_relset_1 @ sk_A @ sk_A @ 
% 17.06/17.31         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 17.06/17.31          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 17.06/17.31         (k6_partfun1 @ sk_A)))),
% 17.06/17.31      inference('sat_resolution*', [status(thm)], ['143', '144'])).
% 17.06/17.31  thf('146', plain, ($false),
% 17.06/17.31      inference('simpl_trail', [status(thm)], ['91', '145'])).
% 17.06/17.31  
% 17.06/17.31  % SZS output end Refutation
% 17.06/17.31  
% 17.06/17.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
