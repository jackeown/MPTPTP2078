%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IFQuVTn0Up

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:40 EST 2020

% Result     : Theorem 3.39s
% Output     : Refutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  193 (1359 expanded)
%              Number of leaves         :   42 ( 410 expanded)
%              Depth                    :   23
%              Number of atoms          : 1427 (22954 expanded)
%              Number of equality atoms :  102 (1420 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t38_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
            & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
            & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ C @ A )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ( ( k2_partfun1 @ X43 @ X44 @ X42 @ X45 )
        = ( k7_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X39 @ X40 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('15',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5','12','13','14'])).

thf('16',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
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

thf('18',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('26',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('27',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('34',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['36','39'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X46 ) @ X47 )
      | ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X46 ) @ X47 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','47'])).

thf('49',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('55',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','55'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('57',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('60',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5','12','13','14'])).

thf('62',plain,
    ( ( ~ ( m1_subset_1 @ ( k7_relat_1 @ k1_xboole_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('64',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('67',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('68',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X17 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('72',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('73',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('76',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('77',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('78',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('79',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('81',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('82',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('83',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('86',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('87',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('89',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['85','90'])).

thf('92',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['71','72'])).

thf('93',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','93'])).

thf('95',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32
       != ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('99',plain,(
    ! [X30: $i] :
      ( zip_tseitin_0 @ X30 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('101',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['97','103'])).

thf('105',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['62','67','74','75','76','77','78','79','80','81','104'])).

thf('106',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('107',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['105','106'])).

thf('108',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['50','107'])).

thf('109',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['48','108'])).

thf('110',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','109'])).

thf('111',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['50','107'])).

thf('112',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['110','111'])).

thf('113',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['23','112'])).

thf('114',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X39 @ X40 @ X38 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('125',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('131',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['129','132'])).

thf('134',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X46 ) @ X47 )
      | ( v1_funct_2 @ X46 @ ( k1_relat_1 @ X46 ) @ X47 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('137',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('138',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['118','138'])).

thf('140',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','139'])).

thf('141',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','117'])).

thf('142',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['129','132'])).

thf('143',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X46 ) @ X47 )
      | ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X46 ) @ X47 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('146',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('147',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['141','147'])).

thf('149',plain,(
    $false ),
    inference(demod,[status(thm)],['140','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IFQuVTn0Up
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:58:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.39/3.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.39/3.57  % Solved by: fo/fo7.sh
% 3.39/3.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.39/3.57  % done 3861 iterations in 3.152s
% 3.39/3.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.39/3.57  % SZS output start Refutation
% 3.39/3.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.39/3.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.39/3.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.39/3.57  thf(sk_C_type, type, sk_C: $i).
% 3.39/3.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.39/3.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.39/3.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.39/3.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.39/3.57  thf(sk_A_type, type, sk_A: $i).
% 3.39/3.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.39/3.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.39/3.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.39/3.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.39/3.57  thf(sk_D_type, type, sk_D: $i).
% 3.39/3.57  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 3.39/3.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.39/3.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.39/3.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.39/3.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.39/3.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.39/3.57  thf(sk_B_type, type, sk_B: $i).
% 3.39/3.57  thf(t38_funct_2, conjecture,
% 3.39/3.57    (![A:$i,B:$i,C:$i,D:$i]:
% 3.39/3.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.39/3.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.39/3.57       ( ( r1_tarski @ C @ A ) =>
% 3.39/3.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 3.39/3.57           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 3.39/3.57             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 3.39/3.57             ( m1_subset_1 @
% 3.39/3.57               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 3.39/3.57               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 3.39/3.57  thf(zf_stmt_0, negated_conjecture,
% 3.39/3.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.39/3.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.39/3.57            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.39/3.57          ( ( r1_tarski @ C @ A ) =>
% 3.39/3.57            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 3.39/3.57              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 3.39/3.57                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 3.39/3.57                ( m1_subset_1 @
% 3.39/3.57                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 3.39/3.57                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 3.39/3.57    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 3.39/3.57  thf('0', plain,
% 3.39/3.57      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 3.39/3.57        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 3.39/3.57             sk_B)
% 3.39/3.57        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 3.39/3.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.57  thf('1', plain,
% 3.39/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.57  thf(redefinition_k2_partfun1, axiom,
% 3.39/3.57    (![A:$i,B:$i,C:$i,D:$i]:
% 3.39/3.57     ( ( ( v1_funct_1 @ C ) & 
% 3.39/3.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.39/3.57       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 3.39/3.57  thf('2', plain,
% 3.39/3.57      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 3.39/3.57         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 3.39/3.57          | ~ (v1_funct_1 @ X42)
% 3.39/3.57          | ((k2_partfun1 @ X43 @ X44 @ X42 @ X45) = (k7_relat_1 @ X42 @ X45)))),
% 3.39/3.57      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 3.39/3.57  thf('3', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 3.39/3.57          | ~ (v1_funct_1 @ sk_D))),
% 3.39/3.57      inference('sup-', [status(thm)], ['1', '2'])).
% 3.39/3.57  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.57  thf('5', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 3.39/3.57      inference('demod', [status(thm)], ['3', '4'])).
% 3.39/3.57  thf('6', plain,
% 3.39/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.57  thf(dt_k2_partfun1, axiom,
% 3.39/3.57    (![A:$i,B:$i,C:$i,D:$i]:
% 3.39/3.57     ( ( ( v1_funct_1 @ C ) & 
% 3.39/3.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.39/3.57       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 3.39/3.57         ( m1_subset_1 @
% 3.39/3.57           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 3.39/3.57           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 3.39/3.57  thf('7', plain,
% 3.39/3.57      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 3.39/3.57         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 3.39/3.57          | ~ (v1_funct_1 @ X38)
% 3.39/3.57          | (v1_funct_1 @ (k2_partfun1 @ X39 @ X40 @ X38 @ X41)))),
% 3.39/3.57      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 3.39/3.57  thf('8', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 3.39/3.57          | ~ (v1_funct_1 @ sk_D))),
% 3.39/3.57      inference('sup-', [status(thm)], ['6', '7'])).
% 3.39/3.57  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.57  thf('10', plain,
% 3.39/3.57      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 3.39/3.57      inference('demod', [status(thm)], ['8', '9'])).
% 3.39/3.57  thf('11', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 3.39/3.57      inference('demod', [status(thm)], ['3', '4'])).
% 3.39/3.57  thf('12', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.39/3.57      inference('demod', [status(thm)], ['10', '11'])).
% 3.39/3.57  thf('13', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 3.39/3.57      inference('demod', [status(thm)], ['3', '4'])).
% 3.39/3.57  thf('14', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 3.39/3.57      inference('demod', [status(thm)], ['3', '4'])).
% 3.39/3.57  thf('15', plain,
% 3.39/3.57      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 3.39/3.57        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 3.39/3.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 3.39/3.57      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 3.39/3.57  thf('16', plain, ((r1_tarski @ sk_C @ sk_A)),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.57  thf('17', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.57  thf(d1_funct_2, axiom,
% 3.39/3.57    (![A:$i,B:$i,C:$i]:
% 3.39/3.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.39/3.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.39/3.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.39/3.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.39/3.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.39/3.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.39/3.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.39/3.57  thf(zf_stmt_1, axiom,
% 3.39/3.57    (![C:$i,B:$i,A:$i]:
% 3.39/3.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.39/3.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.39/3.57  thf('18', plain,
% 3.39/3.57      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.39/3.57         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 3.39/3.57          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 3.39/3.57          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.39/3.57  thf('19', plain,
% 3.39/3.57      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 3.39/3.57        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 3.39/3.57      inference('sup-', [status(thm)], ['17', '18'])).
% 3.39/3.57  thf('20', plain,
% 3.39/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.57  thf(redefinition_k1_relset_1, axiom,
% 3.39/3.57    (![A:$i,B:$i,C:$i]:
% 3.39/3.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.39/3.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.39/3.57  thf('21', plain,
% 3.39/3.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.39/3.57         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 3.39/3.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 3.39/3.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.39/3.57  thf('22', plain,
% 3.39/3.57      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.39/3.57      inference('sup-', [status(thm)], ['20', '21'])).
% 3.39/3.57  thf('23', plain,
% 3.39/3.57      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.39/3.57      inference('demod', [status(thm)], ['19', '22'])).
% 3.39/3.57  thf(zf_stmt_2, axiom,
% 3.39/3.57    (![B:$i,A:$i]:
% 3.39/3.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.39/3.57       ( zip_tseitin_0 @ B @ A ) ))).
% 3.39/3.57  thf('24', plain,
% 3.39/3.57      (![X30 : $i, X31 : $i]:
% 3.39/3.57         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.39/3.57  thf('25', plain,
% 3.39/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.57  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.39/3.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.39/3.57  thf(zf_stmt_5, axiom,
% 3.39/3.57    (![A:$i,B:$i,C:$i]:
% 3.39/3.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.39/3.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.39/3.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.39/3.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.39/3.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.39/3.57  thf('26', plain,
% 3.39/3.57      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.39/3.57         (~ (zip_tseitin_0 @ X35 @ X36)
% 3.39/3.57          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 3.39/3.57          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.39/3.57  thf('27', plain,
% 3.39/3.57      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.39/3.57      inference('sup-', [status(thm)], ['25', '26'])).
% 3.39/3.57  thf('28', plain,
% 3.39/3.57      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 3.39/3.57      inference('sup-', [status(thm)], ['24', '27'])).
% 3.39/3.57  thf('29', plain,
% 3.39/3.57      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.39/3.57      inference('demod', [status(thm)], ['19', '22'])).
% 3.39/3.57  thf('30', plain,
% 3.39/3.57      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.39/3.57      inference('sup-', [status(thm)], ['28', '29'])).
% 3.39/3.57  thf('31', plain,
% 3.39/3.57      (![X30 : $i, X31 : $i]:
% 3.39/3.57         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.39/3.57  thf('32', plain,
% 3.39/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.57  thf(cc2_relset_1, axiom,
% 3.39/3.57    (![A:$i,B:$i,C:$i]:
% 3.39/3.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.39/3.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.39/3.57  thf('33', plain,
% 3.39/3.57      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.39/3.57         ((v5_relat_1 @ X24 @ X26)
% 3.39/3.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 3.39/3.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.39/3.57  thf('34', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 3.39/3.57      inference('sup-', [status(thm)], ['32', '33'])).
% 3.39/3.57  thf(d19_relat_1, axiom,
% 3.39/3.57    (![A:$i,B:$i]:
% 3.39/3.57     ( ( v1_relat_1 @ B ) =>
% 3.39/3.57       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.39/3.57  thf('35', plain,
% 3.39/3.57      (![X11 : $i, X12 : $i]:
% 3.39/3.57         (~ (v5_relat_1 @ X11 @ X12)
% 3.39/3.57          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 3.39/3.57          | ~ (v1_relat_1 @ X11))),
% 3.39/3.57      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.39/3.57  thf('36', plain,
% 3.39/3.57      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 3.39/3.57      inference('sup-', [status(thm)], ['34', '35'])).
% 3.39/3.57  thf('37', plain,
% 3.39/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.57  thf(cc1_relset_1, axiom,
% 3.39/3.57    (![A:$i,B:$i,C:$i]:
% 3.39/3.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.39/3.57       ( v1_relat_1 @ C ) ))).
% 3.39/3.57  thf('38', plain,
% 3.39/3.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.39/3.57         ((v1_relat_1 @ X21)
% 3.39/3.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.39/3.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.39/3.57  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 3.39/3.57      inference('sup-', [status(thm)], ['37', '38'])).
% 3.39/3.57  thf('40', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 3.39/3.57      inference('demod', [status(thm)], ['36', '39'])).
% 3.39/3.57  thf(t4_funct_2, axiom,
% 3.39/3.57    (![A:$i,B:$i]:
% 3.39/3.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.39/3.57       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 3.39/3.57         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 3.39/3.57           ( m1_subset_1 @
% 3.39/3.57             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 3.39/3.57  thf('41', plain,
% 3.39/3.57      (![X46 : $i, X47 : $i]:
% 3.39/3.57         (~ (r1_tarski @ (k2_relat_1 @ X46) @ X47)
% 3.39/3.57          | (m1_subset_1 @ X46 @ 
% 3.39/3.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X46) @ X47)))
% 3.39/3.57          | ~ (v1_funct_1 @ X46)
% 3.39/3.57          | ~ (v1_relat_1 @ X46))),
% 3.39/3.57      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.39/3.57  thf('42', plain,
% 3.39/3.57      ((~ (v1_relat_1 @ sk_D)
% 3.39/3.57        | ~ (v1_funct_1 @ sk_D)
% 3.39/3.57        | (m1_subset_1 @ sk_D @ 
% 3.39/3.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B))))),
% 3.39/3.57      inference('sup-', [status(thm)], ['40', '41'])).
% 3.39/3.57  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 3.39/3.57      inference('sup-', [status(thm)], ['37', '38'])).
% 3.39/3.57  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.57  thf('45', plain,
% 3.39/3.57      ((m1_subset_1 @ sk_D @ 
% 3.39/3.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 3.39/3.57      inference('demod', [status(thm)], ['42', '43', '44'])).
% 3.39/3.57  thf('46', plain,
% 3.39/3.57      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.39/3.57         (~ (zip_tseitin_0 @ X35 @ X36)
% 3.39/3.57          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 3.39/3.57          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.39/3.57  thf('47', plain,
% 3.39/3.57      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D))
% 3.39/3.57        | ~ (zip_tseitin_0 @ sk_B @ (k1_relat_1 @ sk_D)))),
% 3.39/3.57      inference('sup-', [status(thm)], ['45', '46'])).
% 3.39/3.57  thf('48', plain,
% 3.39/3.57      ((((sk_B) = (k1_xboole_0))
% 3.39/3.57        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D)))),
% 3.39/3.57      inference('sup-', [status(thm)], ['31', '47'])).
% 3.39/3.57  thf('49', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.57  thf('50', plain,
% 3.39/3.57      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.39/3.57      inference('split', [status(esa)], ['49'])).
% 3.39/3.57  thf('51', plain,
% 3.39/3.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.57      inference('split', [status(esa)], ['49'])).
% 3.39/3.57  thf('52', plain,
% 3.39/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.57  thf('53', plain,
% 3.39/3.57      (((m1_subset_1 @ sk_D @ 
% 3.39/3.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 3.39/3.57         <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.57      inference('sup+', [status(thm)], ['51', '52'])).
% 3.39/3.57  thf(t113_zfmisc_1, axiom,
% 3.39/3.57    (![A:$i,B:$i]:
% 3.39/3.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.39/3.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.39/3.57  thf('54', plain,
% 3.39/3.57      (![X2 : $i, X3 : $i]:
% 3.39/3.57         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 3.39/3.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.39/3.57  thf('55', plain,
% 3.39/3.57      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 3.39/3.57      inference('simplify', [status(thm)], ['54'])).
% 3.39/3.57  thf('56', plain,
% 3.39/3.57      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 3.39/3.57         <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.57      inference('demod', [status(thm)], ['53', '55'])).
% 3.39/3.57  thf(t3_subset, axiom,
% 3.39/3.57    (![A:$i,B:$i]:
% 3.39/3.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.39/3.57  thf('57', plain,
% 3.39/3.57      (![X5 : $i, X6 : $i]:
% 3.39/3.57         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 3.39/3.57      inference('cnf', [status(esa)], [t3_subset])).
% 3.39/3.57  thf('58', plain,
% 3.39/3.57      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.57      inference('sup-', [status(thm)], ['56', '57'])).
% 3.39/3.57  thf(t3_xboole_1, axiom,
% 3.39/3.57    (![A:$i]:
% 3.39/3.57     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.39/3.57  thf('59', plain,
% 3.39/3.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 3.39/3.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 3.39/3.57  thf('60', plain,
% 3.39/3.57      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.57      inference('sup-', [status(thm)], ['58', '59'])).
% 3.39/3.57  thf('61', plain,
% 3.39/3.57      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 3.39/3.57        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 3.39/3.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 3.39/3.57      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 3.39/3.57  thf('62', plain,
% 3.39/3.57      (((~ (m1_subset_1 @ (k7_relat_1 @ k1_xboole_0 @ sk_C) @ 
% 3.39/3.57            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 3.39/3.57         | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)))
% 3.39/3.57         <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.57      inference('sup-', [status(thm)], ['60', '61'])).
% 3.39/3.57  thf('63', plain,
% 3.39/3.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.57      inference('split', [status(esa)], ['49'])).
% 3.39/3.57  thf('64', plain, ((r1_tarski @ sk_C @ sk_A)),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.57  thf('65', plain,
% 3.39/3.57      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.57      inference('sup+', [status(thm)], ['63', '64'])).
% 3.39/3.57  thf('66', plain,
% 3.39/3.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 3.39/3.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 3.39/3.57  thf('67', plain,
% 3.39/3.57      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.57      inference('sup-', [status(thm)], ['65', '66'])).
% 3.39/3.57  thf(t88_relat_1, axiom,
% 3.39/3.57    (![A:$i,B:$i]:
% 3.39/3.57     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 3.39/3.57  thf('68', plain,
% 3.39/3.57      (![X17 : $i, X18 : $i]:
% 3.39/3.57         ((r1_tarski @ (k7_relat_1 @ X17 @ X18) @ X17) | ~ (v1_relat_1 @ X17))),
% 3.39/3.57      inference('cnf', [status(esa)], [t88_relat_1])).
% 3.39/3.57  thf('69', plain,
% 3.39/3.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 3.39/3.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 3.39/3.57  thf('70', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         (~ (v1_relat_1 @ k1_xboole_0)
% 3.39/3.57          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 3.39/3.57      inference('sup-', [status(thm)], ['68', '69'])).
% 3.39/3.57  thf('71', plain,
% 3.39/3.57      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 3.39/3.57      inference('simplify', [status(thm)], ['54'])).
% 3.39/3.57  thf(fc6_relat_1, axiom,
% 3.39/3.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.39/3.57  thf('72', plain,
% 3.39/3.57      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 3.39/3.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.39/3.57  thf('73', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.39/3.57      inference('sup+', [status(thm)], ['71', '72'])).
% 3.39/3.57  thf('74', plain,
% 3.39/3.57      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.39/3.57      inference('demod', [status(thm)], ['70', '73'])).
% 3.39/3.57  thf('75', plain,
% 3.39/3.57      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.57      inference('sup-', [status(thm)], ['65', '66'])).
% 3.39/3.57  thf('76', plain,
% 3.39/3.57      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 3.39/3.57      inference('simplify', [status(thm)], ['54'])).
% 3.39/3.57  thf(t4_subset_1, axiom,
% 3.39/3.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.39/3.57  thf('77', plain,
% 3.39/3.57      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 3.39/3.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.39/3.57  thf('78', plain,
% 3.39/3.57      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.57      inference('sup-', [status(thm)], ['58', '59'])).
% 3.39/3.57  thf('79', plain,
% 3.39/3.57      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.57      inference('sup-', [status(thm)], ['65', '66'])).
% 3.39/3.57  thf('80', plain,
% 3.39/3.57      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.39/3.57      inference('demod', [status(thm)], ['70', '73'])).
% 3.39/3.57  thf('81', plain,
% 3.39/3.57      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.57      inference('sup-', [status(thm)], ['65', '66'])).
% 3.39/3.57  thf('82', plain,
% 3.39/3.57      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 3.39/3.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.39/3.57  thf('83', plain,
% 3.39/3.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.39/3.57         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 3.39/3.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 3.39/3.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.39/3.57  thf('84', plain,
% 3.39/3.57      (![X0 : $i, X1 : $i]:
% 3.39/3.57         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.39/3.57      inference('sup-', [status(thm)], ['82', '83'])).
% 3.39/3.57  thf('85', plain,
% 3.39/3.57      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.39/3.57      inference('demod', [status(thm)], ['70', '73'])).
% 3.39/3.57  thf('86', plain,
% 3.39/3.57      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 3.39/3.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.39/3.57  thf('87', plain,
% 3.39/3.57      (![X5 : $i, X6 : $i]:
% 3.39/3.57         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 3.39/3.57      inference('cnf', [status(esa)], [t3_subset])).
% 3.39/3.57  thf('88', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.39/3.57      inference('sup-', [status(thm)], ['86', '87'])).
% 3.39/3.57  thf(t91_relat_1, axiom,
% 3.39/3.57    (![A:$i,B:$i]:
% 3.39/3.57     ( ( v1_relat_1 @ B ) =>
% 3.39/3.57       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 3.39/3.57         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 3.39/3.57  thf('89', plain,
% 3.39/3.57      (![X19 : $i, X20 : $i]:
% 3.39/3.57         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 3.39/3.57          | ((k1_relat_1 @ (k7_relat_1 @ X20 @ X19)) = (X19))
% 3.39/3.57          | ~ (v1_relat_1 @ X20))),
% 3.39/3.57      inference('cnf', [status(esa)], [t91_relat_1])).
% 3.39/3.57  thf('90', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         (~ (v1_relat_1 @ X0)
% 3.39/3.57          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 3.39/3.57      inference('sup-', [status(thm)], ['88', '89'])).
% 3.39/3.57  thf('91', plain,
% 3.39/3.57      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 3.39/3.57        | ~ (v1_relat_1 @ k1_xboole_0))),
% 3.39/3.57      inference('sup+', [status(thm)], ['85', '90'])).
% 3.39/3.57  thf('92', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.39/3.57      inference('sup+', [status(thm)], ['71', '72'])).
% 3.39/3.57  thf('93', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.39/3.57      inference('demod', [status(thm)], ['91', '92'])).
% 3.39/3.57  thf('94', plain,
% 3.39/3.57      (![X0 : $i, X1 : $i]:
% 3.39/3.57         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.39/3.57      inference('demod', [status(thm)], ['84', '93'])).
% 3.39/3.57  thf('95', plain,
% 3.39/3.57      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.39/3.57         (((X32) != (k1_relset_1 @ X32 @ X33 @ X34))
% 3.39/3.57          | (v1_funct_2 @ X34 @ X32 @ X33)
% 3.39/3.57          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.39/3.57  thf('96', plain,
% 3.39/3.57      (![X0 : $i, X1 : $i]:
% 3.39/3.57         (((X1) != (k1_xboole_0))
% 3.39/3.57          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 3.39/3.57          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 3.39/3.57      inference('sup-', [status(thm)], ['94', '95'])).
% 3.39/3.57  thf('97', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.39/3.57          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 3.39/3.57      inference('simplify', [status(thm)], ['96'])).
% 3.39/3.57  thf('98', plain,
% 3.39/3.57      (![X30 : $i, X31 : $i]:
% 3.39/3.57         ((zip_tseitin_0 @ X30 @ X31) | ((X31) != (k1_xboole_0)))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.39/3.57  thf('99', plain, (![X30 : $i]: (zip_tseitin_0 @ X30 @ k1_xboole_0)),
% 3.39/3.57      inference('simplify', [status(thm)], ['98'])).
% 3.39/3.57  thf('100', plain,
% 3.39/3.57      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 3.39/3.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.39/3.57  thf('101', plain,
% 3.39/3.57      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.39/3.57         (~ (zip_tseitin_0 @ X35 @ X36)
% 3.39/3.57          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 3.39/3.57          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.39/3.57  thf('102', plain,
% 3.39/3.57      (![X0 : $i, X1 : $i]:
% 3.39/3.57         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 3.39/3.57      inference('sup-', [status(thm)], ['100', '101'])).
% 3.39/3.57  thf('103', plain,
% 3.39/3.57      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 3.39/3.57      inference('sup-', [status(thm)], ['99', '102'])).
% 3.39/3.57  thf('104', plain,
% 3.39/3.57      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.39/3.57      inference('demod', [status(thm)], ['97', '103'])).
% 3.39/3.57  thf('105', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 3.39/3.57      inference('demod', [status(thm)],
% 3.39/3.57                ['62', '67', '74', '75', '76', '77', '78', '79', '80', '81', 
% 3.39/3.57                 '104'])).
% 3.39/3.57  thf('106', plain,
% 3.39/3.57      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 3.39/3.57      inference('split', [status(esa)], ['49'])).
% 3.39/3.57  thf('107', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 3.39/3.57      inference('sat_resolution*', [status(thm)], ['105', '106'])).
% 3.39/3.57  thf('108', plain, (((sk_B) != (k1_xboole_0))),
% 3.39/3.57      inference('simpl_trail', [status(thm)], ['50', '107'])).
% 3.39/3.57  thf('109', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D))),
% 3.39/3.57      inference('simplify_reflect-', [status(thm)], ['48', '108'])).
% 3.39/3.57  thf('110', plain,
% 3.39/3.57      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 3.39/3.57      inference('sup+', [status(thm)], ['30', '109'])).
% 3.39/3.57  thf('111', plain, (((sk_B) != (k1_xboole_0))),
% 3.39/3.57      inference('simpl_trail', [status(thm)], ['50', '107'])).
% 3.39/3.57  thf('112', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 3.39/3.57      inference('simplify_reflect-', [status(thm)], ['110', '111'])).
% 3.39/3.57  thf('113', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.39/3.57      inference('demod', [status(thm)], ['23', '112'])).
% 3.39/3.57  thf('114', plain,
% 3.39/3.57      (![X19 : $i, X20 : $i]:
% 3.39/3.57         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 3.39/3.57          | ((k1_relat_1 @ (k7_relat_1 @ X20 @ X19)) = (X19))
% 3.39/3.57          | ~ (v1_relat_1 @ X20))),
% 3.39/3.57      inference('cnf', [status(esa)], [t91_relat_1])).
% 3.39/3.57  thf('115', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         (~ (r1_tarski @ X0 @ sk_A)
% 3.39/3.57          | ~ (v1_relat_1 @ sk_D)
% 3.39/3.57          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 3.39/3.57      inference('sup-', [status(thm)], ['113', '114'])).
% 3.39/3.57  thf('116', plain, ((v1_relat_1 @ sk_D)),
% 3.39/3.57      inference('sup-', [status(thm)], ['37', '38'])).
% 3.39/3.57  thf('117', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         (~ (r1_tarski @ X0 @ sk_A)
% 3.39/3.57          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 3.39/3.57      inference('demod', [status(thm)], ['115', '116'])).
% 3.39/3.57  thf('118', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 3.39/3.57      inference('sup-', [status(thm)], ['16', '117'])).
% 3.39/3.57  thf('119', plain,
% 3.39/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.57  thf('120', plain,
% 3.39/3.57      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 3.39/3.57         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 3.39/3.57          | ~ (v1_funct_1 @ X38)
% 3.39/3.57          | (m1_subset_1 @ (k2_partfun1 @ X39 @ X40 @ X38 @ X41) @ 
% 3.39/3.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 3.39/3.57      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 3.39/3.57  thf('121', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 3.39/3.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.39/3.57          | ~ (v1_funct_1 @ sk_D))),
% 3.39/3.57      inference('sup-', [status(thm)], ['119', '120'])).
% 3.39/3.57  thf('122', plain, ((v1_funct_1 @ sk_D)),
% 3.39/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.57  thf('123', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 3.39/3.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.39/3.57      inference('demod', [status(thm)], ['121', '122'])).
% 3.39/3.57  thf('124', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 3.39/3.57      inference('demod', [status(thm)], ['3', '4'])).
% 3.39/3.57  thf('125', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.39/3.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.39/3.57      inference('demod', [status(thm)], ['123', '124'])).
% 3.39/3.57  thf('126', plain,
% 3.39/3.57      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.39/3.57         ((v5_relat_1 @ X24 @ X26)
% 3.39/3.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 3.39/3.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.39/3.57  thf('127', plain,
% 3.39/3.57      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 3.39/3.57      inference('sup-', [status(thm)], ['125', '126'])).
% 3.39/3.57  thf('128', plain,
% 3.39/3.57      (![X11 : $i, X12 : $i]:
% 3.39/3.57         (~ (v5_relat_1 @ X11 @ X12)
% 3.39/3.57          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 3.39/3.57          | ~ (v1_relat_1 @ X11))),
% 3.39/3.57      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.39/3.57  thf('129', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 3.39/3.57          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 3.39/3.57      inference('sup-', [status(thm)], ['127', '128'])).
% 3.39/3.57  thf('130', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.39/3.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.39/3.57      inference('demod', [status(thm)], ['123', '124'])).
% 3.39/3.57  thf('131', plain,
% 3.39/3.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.39/3.57         ((v1_relat_1 @ X21)
% 3.39/3.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.39/3.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.39/3.57  thf('132', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.39/3.57      inference('sup-', [status(thm)], ['130', '131'])).
% 3.39/3.57  thf('133', plain,
% 3.39/3.57      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 3.39/3.57      inference('demod', [status(thm)], ['129', '132'])).
% 3.39/3.57  thf('134', plain,
% 3.39/3.57      (![X46 : $i, X47 : $i]:
% 3.39/3.57         (~ (r1_tarski @ (k2_relat_1 @ X46) @ X47)
% 3.39/3.57          | (v1_funct_2 @ X46 @ (k1_relat_1 @ X46) @ X47)
% 3.39/3.57          | ~ (v1_funct_1 @ X46)
% 3.39/3.57          | ~ (v1_relat_1 @ X46))),
% 3.39/3.57      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.39/3.57  thf('135', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 3.39/3.57          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 3.39/3.57          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.39/3.57             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 3.39/3.57      inference('sup-', [status(thm)], ['133', '134'])).
% 3.39/3.57  thf('136', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.39/3.57      inference('sup-', [status(thm)], ['130', '131'])).
% 3.39/3.57  thf('137', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.39/3.57      inference('demod', [status(thm)], ['10', '11'])).
% 3.39/3.57  thf('138', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.39/3.57          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 3.39/3.57      inference('demod', [status(thm)], ['135', '136', '137'])).
% 3.39/3.57  thf('139', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 3.39/3.57      inference('sup+', [status(thm)], ['118', '138'])).
% 3.39/3.57  thf('140', plain,
% 3.39/3.57      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 3.39/3.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 3.39/3.57      inference('demod', [status(thm)], ['15', '139'])).
% 3.39/3.57  thf('141', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 3.39/3.57      inference('sup-', [status(thm)], ['16', '117'])).
% 3.39/3.57  thf('142', plain,
% 3.39/3.57      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 3.39/3.57      inference('demod', [status(thm)], ['129', '132'])).
% 3.39/3.57  thf('143', plain,
% 3.39/3.57      (![X46 : $i, X47 : $i]:
% 3.39/3.57         (~ (r1_tarski @ (k2_relat_1 @ X46) @ X47)
% 3.39/3.57          | (m1_subset_1 @ X46 @ 
% 3.39/3.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X46) @ X47)))
% 3.39/3.57          | ~ (v1_funct_1 @ X46)
% 3.39/3.57          | ~ (v1_relat_1 @ X46))),
% 3.39/3.57      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.39/3.57  thf('144', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 3.39/3.57          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 3.39/3.57          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.39/3.57             (k1_zfmisc_1 @ 
% 3.39/3.57              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 3.39/3.57      inference('sup-', [status(thm)], ['142', '143'])).
% 3.39/3.57  thf('145', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.39/3.57      inference('sup-', [status(thm)], ['130', '131'])).
% 3.39/3.57  thf('146', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.39/3.57      inference('demod', [status(thm)], ['10', '11'])).
% 3.39/3.57  thf('147', plain,
% 3.39/3.57      (![X0 : $i]:
% 3.39/3.57         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.39/3.57          (k1_zfmisc_1 @ 
% 3.39/3.57           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 3.39/3.57      inference('demod', [status(thm)], ['144', '145', '146'])).
% 3.39/3.57  thf('148', plain,
% 3.39/3.57      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 3.39/3.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 3.39/3.57      inference('sup+', [status(thm)], ['141', '147'])).
% 3.39/3.57  thf('149', plain, ($false), inference('demod', [status(thm)], ['140', '148'])).
% 3.39/3.57  
% 3.39/3.57  % SZS output end Refutation
% 3.39/3.57  
% 3.39/3.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
