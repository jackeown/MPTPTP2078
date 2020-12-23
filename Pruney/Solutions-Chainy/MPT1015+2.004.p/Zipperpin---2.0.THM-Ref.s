%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a3w6WZ4Hxr

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:47 EST 2020

% Result     : Theorem 47.50s
% Output     : Refutation 47.50s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 265 expanded)
%              Number of leaves         :   40 (  94 expanded)
%              Depth                    :   14
%              Number of atoms          : 1175 (4747 expanded)
%              Number of equality atoms :   71 ( 122 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t76_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
              & ( v2_funct_1 @ B ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
                & ( v2_funct_1 @ B ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ( ( k1_partfun1 @ X52 @ X53 @ X55 @ X56 @ X51 @ X54 )
        = ( k5_relat_1 @ X51 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
      = ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['1','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('22',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X32 = X35 )
      | ~ ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['11','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
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

thf('29',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('33',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('36',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('37',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('39',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X38 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('40',plain,(
    ! [X37: $i] :
      ( zip_tseitin_0 @ X37 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['41'])).

thf('43',plain,(
    zip_tseitin_1 @ sk_C @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['34','43'])).

thf(t50_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( ( ( k1_relat_1 @ B )
                = A )
              & ( ( k1_relat_1 @ C )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
              & ( v2_funct_1 @ B )
              & ( ( k5_relat_1 @ C @ B )
                = B ) )
           => ( C
              = ( k6_relat_1 @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( X20
        = ( k6_relat_1 @ X21 ) )
      | ( ( k5_relat_1 @ X20 @ X22 )
       != X22 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ( ( k1_relat_1 @ X20 )
       != X21 )
      | ~ ( v2_funct_1 @ X22 )
      | ( ( k1_relat_1 @ X22 )
       != X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t50_funct_1])).

thf('46',plain,(
    ! [X20: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( ( k1_relat_1 @ X22 )
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v2_funct_1 @ X22 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ ( k1_relat_1 @ X20 ) )
      | ( ( k5_relat_1 @ X20 @ X22 )
       != X22 )
      | ( X20
        = ( k6_relat_1 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('47',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('48',plain,(
    ! [X20: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( ( k1_relat_1 @ X22 )
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v2_funct_1 @ X22 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ ( k1_relat_1 @ X20 ) )
      | ( ( k5_relat_1 @ X20 @ X22 )
       != X22 )
      | ( X20
        = ( k6_partfun1 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_C
        = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v5_relat_1 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('52',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['50','51'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('56',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['55','56'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['34','43'])).

thf('62',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['34','43'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k6_partfun1 @ sk_A ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','58','59','60','61','62'])).

thf('64',plain,
    ( ( sk_B != sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('71',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('74',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('78',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['41'])).

thf('80',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['75','80'])).

thf('82',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( sk_B != sk_B )
    | ( sk_A != sk_A )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','67','68','81','82'])).

thf('84',plain,
    ( sk_C
    = ( k6_partfun1 @ sk_A ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 )
      | ( X32 != X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('87',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r2_relset_1 @ X33 @ X34 @ X35 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['0','84','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a3w6WZ4Hxr
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:37:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 47.50/47.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 47.50/47.74  % Solved by: fo/fo7.sh
% 47.50/47.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 47.50/47.74  % done 10209 iterations in 47.275s
% 47.50/47.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 47.50/47.74  % SZS output start Refutation
% 47.50/47.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 47.50/47.74  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 47.50/47.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 47.50/47.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 47.50/47.74  thf(sk_C_type, type, sk_C: $i).
% 47.50/47.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 47.50/47.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 47.50/47.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 47.50/47.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 47.50/47.74  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 47.50/47.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 47.50/47.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 47.50/47.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 47.50/47.74  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 47.50/47.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 47.50/47.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 47.50/47.74  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 47.50/47.74  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 47.50/47.74  thf(sk_A_type, type, sk_A: $i).
% 47.50/47.74  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 47.50/47.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 47.50/47.74  thf(sk_B_type, type, sk_B: $i).
% 47.50/47.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 47.50/47.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 47.50/47.74  thf(t76_funct_2, conjecture,
% 47.50/47.74    (![A:$i,B:$i]:
% 47.50/47.74     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 47.50/47.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 47.50/47.74       ( ![C:$i]:
% 47.50/47.74         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 47.50/47.74             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 47.50/47.74           ( ( ( r2_relset_1 @
% 47.50/47.74                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 47.50/47.74               ( v2_funct_1 @ B ) ) =>
% 47.50/47.74             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 47.50/47.74  thf(zf_stmt_0, negated_conjecture,
% 47.50/47.74    (~( ![A:$i,B:$i]:
% 47.50/47.74        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 47.50/47.74            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 47.50/47.74          ( ![C:$i]:
% 47.50/47.74            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 47.50/47.74                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 47.50/47.74              ( ( ( r2_relset_1 @
% 47.50/47.74                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 47.50/47.74                  ( v2_funct_1 @ B ) ) =>
% 47.50/47.74                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 47.50/47.74    inference('cnf.neg', [status(esa)], [t76_funct_2])).
% 47.50/47.74  thf('0', plain,
% 47.50/47.74      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf('1', plain,
% 47.50/47.74      ((r2_relset_1 @ sk_A @ sk_A @ 
% 47.50/47.74        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf('2', plain,
% 47.50/47.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf('3', plain,
% 47.50/47.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf(redefinition_k1_partfun1, axiom,
% 47.50/47.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 47.50/47.74     ( ( ( v1_funct_1 @ E ) & 
% 47.50/47.74         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 47.50/47.74         ( v1_funct_1 @ F ) & 
% 47.50/47.74         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 47.50/47.74       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 47.50/47.74  thf('4', plain,
% 47.50/47.74      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 47.50/47.74         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 47.50/47.74          | ~ (v1_funct_1 @ X51)
% 47.50/47.74          | ~ (v1_funct_1 @ X54)
% 47.50/47.74          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 47.50/47.74          | ((k1_partfun1 @ X52 @ X53 @ X55 @ X56 @ X51 @ X54)
% 47.50/47.74              = (k5_relat_1 @ X51 @ X54)))),
% 47.50/47.74      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 47.50/47.74  thf('5', plain,
% 47.50/47.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.50/47.74         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 47.50/47.74            = (k5_relat_1 @ sk_C @ X0))
% 47.50/47.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 47.50/47.74          | ~ (v1_funct_1 @ X0)
% 47.50/47.74          | ~ (v1_funct_1 @ sk_C))),
% 47.50/47.74      inference('sup-', [status(thm)], ['3', '4'])).
% 47.50/47.74  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf('7', plain,
% 47.50/47.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.50/47.74         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 47.50/47.74            = (k5_relat_1 @ sk_C @ X0))
% 47.50/47.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 47.50/47.74          | ~ (v1_funct_1 @ X0))),
% 47.50/47.74      inference('demod', [status(thm)], ['5', '6'])).
% 47.50/47.74  thf('8', plain,
% 47.50/47.74      ((~ (v1_funct_1 @ sk_B)
% 47.50/47.74        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 47.50/47.74            = (k5_relat_1 @ sk_C @ sk_B)))),
% 47.50/47.74      inference('sup-', [status(thm)], ['2', '7'])).
% 47.50/47.74  thf('9', plain, ((v1_funct_1 @ sk_B)),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf('10', plain,
% 47.50/47.74      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 47.50/47.74         = (k5_relat_1 @ sk_C @ sk_B))),
% 47.50/47.74      inference('demod', [status(thm)], ['8', '9'])).
% 47.50/47.74  thf('11', plain,
% 47.50/47.74      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ sk_B)),
% 47.50/47.74      inference('demod', [status(thm)], ['1', '10'])).
% 47.50/47.74  thf('12', plain,
% 47.50/47.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf('13', plain,
% 47.50/47.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf(dt_k1_partfun1, axiom,
% 47.50/47.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 47.50/47.74     ( ( ( v1_funct_1 @ E ) & 
% 47.50/47.74         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 47.50/47.74         ( v1_funct_1 @ F ) & 
% 47.50/47.74         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 47.50/47.74       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 47.50/47.74         ( m1_subset_1 @
% 47.50/47.74           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 47.50/47.74           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 47.50/47.74  thf('14', plain,
% 47.50/47.74      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 47.50/47.74         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 47.50/47.74          | ~ (v1_funct_1 @ X45)
% 47.50/47.74          | ~ (v1_funct_1 @ X48)
% 47.50/47.74          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 47.50/47.74          | (m1_subset_1 @ (k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48) @ 
% 47.50/47.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X50))))),
% 47.50/47.74      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 47.50/47.74  thf('15', plain,
% 47.50/47.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.50/47.74         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 47.50/47.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 47.50/47.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 47.50/47.74          | ~ (v1_funct_1 @ X1)
% 47.50/47.74          | ~ (v1_funct_1 @ sk_C))),
% 47.50/47.74      inference('sup-', [status(thm)], ['13', '14'])).
% 47.50/47.74  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf('17', plain,
% 47.50/47.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.50/47.74         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 47.50/47.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 47.50/47.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 47.50/47.74          | ~ (v1_funct_1 @ X1))),
% 47.50/47.74      inference('demod', [status(thm)], ['15', '16'])).
% 47.50/47.74  thf('18', plain,
% 47.50/47.74      ((~ (v1_funct_1 @ sk_B)
% 47.50/47.74        | (m1_subset_1 @ 
% 47.50/47.74           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 47.50/47.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 47.50/47.74      inference('sup-', [status(thm)], ['12', '17'])).
% 47.50/47.74  thf('19', plain, ((v1_funct_1 @ sk_B)),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf('20', plain,
% 47.50/47.74      ((m1_subset_1 @ 
% 47.50/47.74        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 47.50/47.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.50/47.74      inference('demod', [status(thm)], ['18', '19'])).
% 47.50/47.74  thf('21', plain,
% 47.50/47.74      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 47.50/47.74         = (k5_relat_1 @ sk_C @ sk_B))),
% 47.50/47.74      inference('demod', [status(thm)], ['8', '9'])).
% 47.50/47.74  thf('22', plain,
% 47.50/47.74      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_B) @ 
% 47.50/47.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.50/47.74      inference('demod', [status(thm)], ['20', '21'])).
% 47.50/47.74  thf(redefinition_r2_relset_1, axiom,
% 47.50/47.74    (![A:$i,B:$i,C:$i,D:$i]:
% 47.50/47.74     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 47.50/47.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 47.50/47.74       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 47.50/47.74  thf('23', plain,
% 47.50/47.74      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 47.50/47.74         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 47.50/47.74          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 47.50/47.74          | ((X32) = (X35))
% 47.50/47.74          | ~ (r2_relset_1 @ X33 @ X34 @ X32 @ X35))),
% 47.50/47.74      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 47.50/47.74  thf('24', plain,
% 47.50/47.74      (![X0 : $i]:
% 47.50/47.74         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ X0)
% 47.50/47.74          | ((k5_relat_1 @ sk_C @ sk_B) = (X0))
% 47.50/47.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 47.50/47.74      inference('sup-', [status(thm)], ['22', '23'])).
% 47.50/47.74  thf('25', plain,
% 47.50/47.74      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 47.50/47.74        | ((k5_relat_1 @ sk_C @ sk_B) = (sk_B)))),
% 47.50/47.74      inference('sup-', [status(thm)], ['11', '24'])).
% 47.50/47.74  thf('26', plain,
% 47.50/47.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf('27', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 47.50/47.74      inference('demod', [status(thm)], ['25', '26'])).
% 47.50/47.74  thf('28', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf(d1_funct_2, axiom,
% 47.50/47.74    (![A:$i,B:$i,C:$i]:
% 47.50/47.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 47.50/47.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 47.50/47.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 47.50/47.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 47.50/47.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 47.50/47.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 47.50/47.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 47.50/47.74  thf(zf_stmt_1, axiom,
% 47.50/47.74    (![C:$i,B:$i,A:$i]:
% 47.50/47.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 47.50/47.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 47.50/47.74  thf('29', plain,
% 47.50/47.74      (![X39 : $i, X40 : $i, X41 : $i]:
% 47.50/47.74         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 47.50/47.74          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 47.50/47.74          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 47.50/47.74  thf('30', plain,
% 47.50/47.74      ((~ (zip_tseitin_1 @ sk_C @ sk_A @ sk_A)
% 47.50/47.74        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_C)))),
% 47.50/47.74      inference('sup-', [status(thm)], ['28', '29'])).
% 47.50/47.74  thf('31', plain,
% 47.50/47.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf(redefinition_k1_relset_1, axiom,
% 47.50/47.74    (![A:$i,B:$i,C:$i]:
% 47.50/47.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 47.50/47.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 47.50/47.74  thf('32', plain,
% 47.50/47.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 47.50/47.74         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 47.50/47.74          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 47.50/47.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 47.50/47.74  thf('33', plain,
% 47.50/47.74      (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 47.50/47.74      inference('sup-', [status(thm)], ['31', '32'])).
% 47.50/47.74  thf('34', plain,
% 47.50/47.74      ((~ (zip_tseitin_1 @ sk_C @ sk_A @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 47.50/47.74      inference('demod', [status(thm)], ['30', '33'])).
% 47.50/47.74  thf('35', plain,
% 47.50/47.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 47.50/47.74  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 47.50/47.74  thf(zf_stmt_4, axiom,
% 47.50/47.74    (![B:$i,A:$i]:
% 47.50/47.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 47.50/47.74       ( zip_tseitin_0 @ B @ A ) ))).
% 47.50/47.74  thf(zf_stmt_5, axiom,
% 47.50/47.74    (![A:$i,B:$i,C:$i]:
% 47.50/47.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 47.50/47.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 47.50/47.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 47.50/47.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 47.50/47.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 47.50/47.74  thf('36', plain,
% 47.50/47.74      (![X42 : $i, X43 : $i, X44 : $i]:
% 47.50/47.74         (~ (zip_tseitin_0 @ X42 @ X43)
% 47.50/47.74          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 47.50/47.74          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 47.50/47.74  thf('37', plain,
% 47.50/47.74      (((zip_tseitin_1 @ sk_C @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 47.50/47.74      inference('sup-', [status(thm)], ['35', '36'])).
% 47.50/47.74  thf('38', plain,
% 47.50/47.74      (![X37 : $i, X38 : $i]:
% 47.50/47.74         ((zip_tseitin_0 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 47.50/47.74  thf('39', plain,
% 47.50/47.74      (![X37 : $i, X38 : $i]:
% 47.50/47.74         ((zip_tseitin_0 @ X37 @ X38) | ((X38) != (k1_xboole_0)))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 47.50/47.74  thf('40', plain, (![X37 : $i]: (zip_tseitin_0 @ X37 @ k1_xboole_0)),
% 47.50/47.74      inference('simplify', [status(thm)], ['39'])).
% 47.50/47.74  thf('41', plain,
% 47.50/47.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.50/47.74         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 47.50/47.74      inference('sup+', [status(thm)], ['38', '40'])).
% 47.50/47.74  thf('42', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 47.50/47.74      inference('eq_fact', [status(thm)], ['41'])).
% 47.50/47.74  thf('43', plain, ((zip_tseitin_1 @ sk_C @ sk_A @ sk_A)),
% 47.50/47.74      inference('demod', [status(thm)], ['37', '42'])).
% 47.50/47.74  thf('44', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 47.50/47.74      inference('demod', [status(thm)], ['34', '43'])).
% 47.50/47.74  thf(t50_funct_1, axiom,
% 47.50/47.74    (![A:$i,B:$i]:
% 47.50/47.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 47.50/47.74       ( ![C:$i]:
% 47.50/47.74         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 47.50/47.74           ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 47.50/47.74               ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 47.50/47.74               ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & ( v2_funct_1 @ B ) & 
% 47.50/47.74               ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 47.50/47.74             ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ))).
% 47.50/47.74  thf('45', plain,
% 47.50/47.74      (![X20 : $i, X21 : $i, X22 : $i]:
% 47.50/47.74         (~ (v1_relat_1 @ X20)
% 47.50/47.74          | ~ (v1_funct_1 @ X20)
% 47.50/47.74          | ((X20) = (k6_relat_1 @ X21))
% 47.50/47.74          | ((k5_relat_1 @ X20 @ X22) != (X22))
% 47.50/47.74          | ~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 47.50/47.74          | ((k1_relat_1 @ X20) != (X21))
% 47.50/47.74          | ~ (v2_funct_1 @ X22)
% 47.50/47.74          | ((k1_relat_1 @ X22) != (X21))
% 47.50/47.74          | ~ (v1_funct_1 @ X22)
% 47.50/47.74          | ~ (v1_relat_1 @ X22))),
% 47.50/47.74      inference('cnf', [status(esa)], [t50_funct_1])).
% 47.50/47.74  thf('46', plain,
% 47.50/47.74      (![X20 : $i, X22 : $i]:
% 47.50/47.74         (~ (v1_relat_1 @ X22)
% 47.50/47.74          | ~ (v1_funct_1 @ X22)
% 47.50/47.74          | ((k1_relat_1 @ X22) != (k1_relat_1 @ X20))
% 47.50/47.74          | ~ (v2_funct_1 @ X22)
% 47.50/47.74          | ~ (r1_tarski @ (k2_relat_1 @ X20) @ (k1_relat_1 @ X20))
% 47.50/47.74          | ((k5_relat_1 @ X20 @ X22) != (X22))
% 47.50/47.74          | ((X20) = (k6_relat_1 @ (k1_relat_1 @ X20)))
% 47.50/47.74          | ~ (v1_funct_1 @ X20)
% 47.50/47.74          | ~ (v1_relat_1 @ X20))),
% 47.50/47.74      inference('simplify', [status(thm)], ['45'])).
% 47.50/47.74  thf(redefinition_k6_partfun1, axiom,
% 47.50/47.74    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 47.50/47.74  thf('47', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 47.50/47.74      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 47.50/47.74  thf('48', plain,
% 47.50/47.74      (![X20 : $i, X22 : $i]:
% 47.50/47.74         (~ (v1_relat_1 @ X22)
% 47.50/47.74          | ~ (v1_funct_1 @ X22)
% 47.50/47.74          | ((k1_relat_1 @ X22) != (k1_relat_1 @ X20))
% 47.50/47.74          | ~ (v2_funct_1 @ X22)
% 47.50/47.74          | ~ (r1_tarski @ (k2_relat_1 @ X20) @ (k1_relat_1 @ X20))
% 47.50/47.74          | ((k5_relat_1 @ X20 @ X22) != (X22))
% 47.50/47.74          | ((X20) = (k6_partfun1 @ (k1_relat_1 @ X20)))
% 47.50/47.74          | ~ (v1_funct_1 @ X20)
% 47.50/47.74          | ~ (v1_relat_1 @ X20))),
% 47.50/47.74      inference('demod', [status(thm)], ['46', '47'])).
% 47.50/47.74  thf('49', plain,
% 47.50/47.74      (![X0 : $i]:
% 47.50/47.74         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)
% 47.50/47.74          | ~ (v1_relat_1 @ sk_C)
% 47.50/47.74          | ~ (v1_funct_1 @ sk_C)
% 47.50/47.74          | ((sk_C) = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 47.50/47.74          | ((k5_relat_1 @ sk_C @ X0) != (X0))
% 47.50/47.74          | ~ (v2_funct_1 @ X0)
% 47.50/47.74          | ((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 47.50/47.74          | ~ (v1_funct_1 @ X0)
% 47.50/47.74          | ~ (v1_relat_1 @ X0))),
% 47.50/47.74      inference('sup-', [status(thm)], ['44', '48'])).
% 47.50/47.74  thf('50', plain,
% 47.50/47.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf(cc2_relset_1, axiom,
% 47.50/47.74    (![A:$i,B:$i,C:$i]:
% 47.50/47.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 47.50/47.74       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 47.50/47.74  thf('51', plain,
% 47.50/47.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 47.50/47.74         ((v5_relat_1 @ X26 @ X28)
% 47.50/47.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 47.50/47.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 47.50/47.74  thf('52', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 47.50/47.74      inference('sup-', [status(thm)], ['50', '51'])).
% 47.50/47.74  thf(d19_relat_1, axiom,
% 47.50/47.74    (![A:$i,B:$i]:
% 47.50/47.74     ( ( v1_relat_1 @ B ) =>
% 47.50/47.74       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 47.50/47.74  thf('53', plain,
% 47.50/47.74      (![X13 : $i, X14 : $i]:
% 47.50/47.74         (~ (v5_relat_1 @ X13 @ X14)
% 47.50/47.74          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 47.50/47.74          | ~ (v1_relat_1 @ X13))),
% 47.50/47.74      inference('cnf', [status(esa)], [d19_relat_1])).
% 47.50/47.74  thf('54', plain,
% 47.50/47.74      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 47.50/47.74      inference('sup-', [status(thm)], ['52', '53'])).
% 47.50/47.74  thf('55', plain,
% 47.50/47.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf(cc1_relset_1, axiom,
% 47.50/47.74    (![A:$i,B:$i,C:$i]:
% 47.50/47.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 47.50/47.74       ( v1_relat_1 @ C ) ))).
% 47.50/47.74  thf('56', plain,
% 47.50/47.74      (![X23 : $i, X24 : $i, X25 : $i]:
% 47.50/47.74         ((v1_relat_1 @ X23)
% 47.50/47.74          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 47.50/47.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 47.50/47.74  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 47.50/47.74      inference('sup-', [status(thm)], ['55', '56'])).
% 47.50/47.74  thf('58', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 47.50/47.74      inference('demod', [status(thm)], ['54', '57'])).
% 47.50/47.74  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 47.50/47.74      inference('sup-', [status(thm)], ['55', '56'])).
% 47.50/47.74  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf('61', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 47.50/47.74      inference('demod', [status(thm)], ['34', '43'])).
% 47.50/47.74  thf('62', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 47.50/47.74      inference('demod', [status(thm)], ['34', '43'])).
% 47.50/47.74  thf('63', plain,
% 47.50/47.74      (![X0 : $i]:
% 47.50/47.74         (((sk_C) = (k6_partfun1 @ sk_A))
% 47.50/47.74          | ((k5_relat_1 @ sk_C @ X0) != (X0))
% 47.50/47.74          | ~ (v2_funct_1 @ X0)
% 47.50/47.74          | ((k1_relat_1 @ X0) != (sk_A))
% 47.50/47.74          | ~ (v1_funct_1 @ X0)
% 47.50/47.74          | ~ (v1_relat_1 @ X0))),
% 47.50/47.74      inference('demod', [status(thm)], ['49', '58', '59', '60', '61', '62'])).
% 47.50/47.74  thf('64', plain,
% 47.50/47.74      ((((sk_B) != (sk_B))
% 47.50/47.74        | ~ (v1_relat_1 @ sk_B)
% 47.50/47.74        | ~ (v1_funct_1 @ sk_B)
% 47.50/47.74        | ((k1_relat_1 @ sk_B) != (sk_A))
% 47.50/47.74        | ~ (v2_funct_1 @ sk_B)
% 47.50/47.74        | ((sk_C) = (k6_partfun1 @ sk_A)))),
% 47.50/47.74      inference('sup-', [status(thm)], ['27', '63'])).
% 47.50/47.74  thf('65', plain,
% 47.50/47.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf('66', plain,
% 47.50/47.74      (![X23 : $i, X24 : $i, X25 : $i]:
% 47.50/47.74         ((v1_relat_1 @ X23)
% 47.50/47.74          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 47.50/47.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 47.50/47.74  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 47.50/47.74      inference('sup-', [status(thm)], ['65', '66'])).
% 47.50/47.74  thf('68', plain, ((v1_funct_1 @ sk_B)),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf('69', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf('70', plain,
% 47.50/47.74      (![X39 : $i, X40 : $i, X41 : $i]:
% 47.50/47.74         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 47.50/47.74          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 47.50/47.74          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 47.50/47.74  thf('71', plain,
% 47.50/47.74      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 47.50/47.74        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 47.50/47.74      inference('sup-', [status(thm)], ['69', '70'])).
% 47.50/47.74  thf('72', plain,
% 47.50/47.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf('73', plain,
% 47.50/47.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 47.50/47.74         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 47.50/47.74          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 47.50/47.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 47.50/47.74  thf('74', plain,
% 47.50/47.74      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 47.50/47.74      inference('sup-', [status(thm)], ['72', '73'])).
% 47.50/47.74  thf('75', plain,
% 47.50/47.74      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_B)))),
% 47.50/47.74      inference('demod', [status(thm)], ['71', '74'])).
% 47.50/47.74  thf('76', plain,
% 47.50/47.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf('77', plain,
% 47.50/47.74      (![X42 : $i, X43 : $i, X44 : $i]:
% 47.50/47.74         (~ (zip_tseitin_0 @ X42 @ X43)
% 47.50/47.74          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 47.50/47.74          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 47.50/47.74  thf('78', plain,
% 47.50/47.74      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 47.50/47.74      inference('sup-', [status(thm)], ['76', '77'])).
% 47.50/47.74  thf('79', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 47.50/47.74      inference('eq_fact', [status(thm)], ['41'])).
% 47.50/47.74  thf('80', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 47.50/47.74      inference('demod', [status(thm)], ['78', '79'])).
% 47.50/47.74  thf('81', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 47.50/47.74      inference('demod', [status(thm)], ['75', '80'])).
% 47.50/47.74  thf('82', plain, ((v2_funct_1 @ sk_B)),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf('83', plain,
% 47.50/47.74      ((((sk_B) != (sk_B))
% 47.50/47.74        | ((sk_A) != (sk_A))
% 47.50/47.74        | ((sk_C) = (k6_partfun1 @ sk_A)))),
% 47.50/47.74      inference('demod', [status(thm)], ['64', '67', '68', '81', '82'])).
% 47.50/47.74  thf('84', plain, (((sk_C) = (k6_partfun1 @ sk_A))),
% 47.50/47.74      inference('simplify', [status(thm)], ['83'])).
% 47.50/47.74  thf('85', plain,
% 47.50/47.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.50/47.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.50/47.74  thf('86', plain,
% 47.50/47.74      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 47.50/47.74         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 47.50/47.74          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 47.50/47.74          | (r2_relset_1 @ X33 @ X34 @ X32 @ X35)
% 47.50/47.74          | ((X32) != (X35)))),
% 47.50/47.74      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 47.50/47.74  thf('87', plain,
% 47.50/47.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 47.50/47.74         ((r2_relset_1 @ X33 @ X34 @ X35 @ X35)
% 47.50/47.74          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 47.50/47.74      inference('simplify', [status(thm)], ['86'])).
% 47.50/47.74  thf('88', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 47.50/47.74      inference('sup-', [status(thm)], ['85', '87'])).
% 47.50/47.74  thf('89', plain, ($false),
% 47.50/47.74      inference('demod', [status(thm)], ['0', '84', '88'])).
% 47.50/47.74  
% 47.50/47.74  % SZS output end Refutation
% 47.50/47.74  
% 47.50/47.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
