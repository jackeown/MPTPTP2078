%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c281qAWcoZ

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:41 EST 2020

% Result     : Theorem 2.72s
% Output     : Refutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 191 expanded)
%              Number of leaves         :   43 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  998 (3874 expanded)
%              Number of equality atoms :   69 ( 288 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t20_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( ( k2_relset_1 @ B @ C @ E )
                = C ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ D )
                  = B )
                & ( ( k2_relset_1 @ B @ C @ E )
                  = C ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 )
        = ( k5_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','7','16'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('22',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k8_relset_1 @ X18 @ X19 @ X20 @ X19 )
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('27',plain,
    ( ( k8_relset_1 @ sk_B @ sk_C @ sk_E @ sk_C )
    = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('29',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k8_relset_1 @ X15 @ X16 @ X14 @ X17 )
        = ( k10_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_C @ sk_E @ X0 )
      = ( k10_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
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

thf('32',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('36',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('37',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['33','40'])).

thf('42',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['27','30','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X5: $i] :
      ( ( ( k10_relat_1 @ X5 @ ( k2_relat_1 @ X5 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('49',plain,
    ( ( ( k10_relat_1 @ sk_E @ sk_C )
      = ( k1_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('52',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['42','53'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('55',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        = ( k2_relat_1 @ sk_E ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['50','51'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference('sup+',[status(thm)],['45','46'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        = sk_C )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['24','59'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('61',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('63',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('68',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['60','65','68'])).

thf('70',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['19','69'])).

thf('71',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('73',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c281qAWcoZ
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.72/2.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.72/2.91  % Solved by: fo/fo7.sh
% 2.72/2.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.72/2.91  % done 1263 iterations in 2.452s
% 2.72/2.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.72/2.91  % SZS output start Refutation
% 2.72/2.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.72/2.91  thf(sk_C_type, type, sk_C: $i).
% 2.72/2.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.72/2.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.72/2.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.72/2.91  thf(sk_A_type, type, sk_A: $i).
% 2.72/2.91  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.72/2.91  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 2.72/2.91  thf(sk_B_type, type, sk_B: $i).
% 2.72/2.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.72/2.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.72/2.91  thf(sk_D_type, type, sk_D: $i).
% 2.72/2.91  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 2.72/2.91  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.72/2.91  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.72/2.91  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 2.72/2.91  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.72/2.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.72/2.91  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.72/2.91  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.72/2.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.72/2.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.72/2.91  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.72/2.91  thf(sk_E_type, type, sk_E: $i).
% 2.72/2.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.72/2.91  thf(t20_funct_2, conjecture,
% 2.72/2.91    (![A:$i,B:$i,C:$i,D:$i]:
% 2.72/2.91     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.72/2.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.72/2.91       ( ![E:$i]:
% 2.72/2.91         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.72/2.91             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.72/2.91           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.72/2.91               ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 2.72/2.91             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.72/2.91               ( ( k2_relset_1 @
% 2.72/2.91                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.72/2.91                 ( C ) ) ) ) ) ) ))).
% 2.72/2.91  thf(zf_stmt_0, negated_conjecture,
% 2.72/2.91    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.72/2.91        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.72/2.91            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.72/2.91          ( ![E:$i]:
% 2.72/2.91            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.72/2.91                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.72/2.91              ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.72/2.91                  ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 2.72/2.91                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.72/2.91                  ( ( k2_relset_1 @
% 2.72/2.91                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.72/2.91                    ( C ) ) ) ) ) ) ) )),
% 2.72/2.91    inference('cnf.neg', [status(esa)], [t20_funct_2])).
% 2.72/2.91  thf('0', plain,
% 2.72/2.91      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf('1', plain,
% 2.72/2.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf(dt_k1_partfun1, axiom,
% 2.72/2.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.72/2.91     ( ( ( v1_funct_1 @ E ) & 
% 2.72/2.91         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.72/2.91         ( v1_funct_1 @ F ) & 
% 2.72/2.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.72/2.91       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.72/2.91         ( m1_subset_1 @
% 2.72/2.91           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.72/2.91           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.72/2.91  thf('2', plain,
% 2.72/2.91      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 2.72/2.91         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.72/2.91          | ~ (v1_funct_1 @ X29)
% 2.72/2.91          | ~ (v1_funct_1 @ X32)
% 2.72/2.91          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 2.72/2.91          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 2.72/2.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 2.72/2.91      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.72/2.91  thf('3', plain,
% 2.72/2.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 2.72/2.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.72/2.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.72/2.91          | ~ (v1_funct_1 @ X1)
% 2.72/2.91          | ~ (v1_funct_1 @ sk_D))),
% 2.72/2.91      inference('sup-', [status(thm)], ['1', '2'])).
% 2.72/2.91  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf('5', plain,
% 2.72/2.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 2.72/2.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.72/2.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.72/2.91          | ~ (v1_funct_1 @ X1))),
% 2.72/2.91      inference('demod', [status(thm)], ['3', '4'])).
% 2.72/2.91  thf('6', plain,
% 2.72/2.91      ((~ (v1_funct_1 @ sk_E)
% 2.72/2.91        | (m1_subset_1 @ 
% 2.72/2.91           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 2.72/2.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 2.72/2.91      inference('sup-', [status(thm)], ['0', '5'])).
% 2.72/2.91  thf('7', plain, ((v1_funct_1 @ sk_E)),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf('8', plain,
% 2.72/2.91      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf('9', plain,
% 2.72/2.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf(redefinition_k1_partfun1, axiom,
% 2.72/2.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.72/2.91     ( ( ( v1_funct_1 @ E ) & 
% 2.72/2.91         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.72/2.91         ( v1_funct_1 @ F ) & 
% 2.72/2.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.72/2.91       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.72/2.91  thf('10', plain,
% 2.72/2.91      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 2.72/2.91         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 2.72/2.91          | ~ (v1_funct_1 @ X35)
% 2.72/2.91          | ~ (v1_funct_1 @ X38)
% 2.72/2.91          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 2.72/2.91          | ((k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38)
% 2.72/2.91              = (k5_relat_1 @ X35 @ X38)))),
% 2.72/2.91      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.72/2.91  thf('11', plain,
% 2.72/2.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.91         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.72/2.91            = (k5_relat_1 @ sk_D @ X0))
% 2.72/2.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.72/2.91          | ~ (v1_funct_1 @ X0)
% 2.72/2.91          | ~ (v1_funct_1 @ sk_D))),
% 2.72/2.91      inference('sup-', [status(thm)], ['9', '10'])).
% 2.72/2.91  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf('13', plain,
% 2.72/2.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.91         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.72/2.91            = (k5_relat_1 @ sk_D @ X0))
% 2.72/2.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.72/2.91          | ~ (v1_funct_1 @ X0))),
% 2.72/2.91      inference('demod', [status(thm)], ['11', '12'])).
% 2.72/2.91  thf('14', plain,
% 2.72/2.91      ((~ (v1_funct_1 @ sk_E)
% 2.72/2.91        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.72/2.91            = (k5_relat_1 @ sk_D @ sk_E)))),
% 2.72/2.91      inference('sup-', [status(thm)], ['8', '13'])).
% 2.72/2.91  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf('16', plain,
% 2.72/2.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.72/2.91         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.72/2.91      inference('demod', [status(thm)], ['14', '15'])).
% 2.72/2.91  thf('17', plain,
% 2.72/2.91      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 2.72/2.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.72/2.91      inference('demod', [status(thm)], ['6', '7', '16'])).
% 2.72/2.91  thf(redefinition_k2_relset_1, axiom,
% 2.72/2.91    (![A:$i,B:$i,C:$i]:
% 2.72/2.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.72/2.91       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.72/2.91  thf('18', plain,
% 2.72/2.91      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.72/2.91         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 2.72/2.91          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 2.72/2.91      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.72/2.91  thf('19', plain,
% 2.72/2.91      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 2.72/2.91         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 2.72/2.91      inference('sup-', [status(thm)], ['17', '18'])).
% 2.72/2.91  thf('20', plain,
% 2.72/2.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf('21', plain,
% 2.72/2.91      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.72/2.91         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 2.72/2.91          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 2.72/2.91      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.72/2.91  thf('22', plain,
% 2.72/2.91      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.72/2.91      inference('sup-', [status(thm)], ['20', '21'])).
% 2.72/2.91  thf('23', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_B))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf('24', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 2.72/2.91      inference('sup+', [status(thm)], ['22', '23'])).
% 2.72/2.91  thf('25', plain,
% 2.72/2.91      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf(t38_relset_1, axiom,
% 2.72/2.91    (![A:$i,B:$i,C:$i]:
% 2.72/2.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.72/2.91       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 2.72/2.91         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.72/2.91  thf('26', plain,
% 2.72/2.91      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.72/2.91         (((k8_relset_1 @ X18 @ X19 @ X20 @ X19)
% 2.72/2.91            = (k1_relset_1 @ X18 @ X19 @ X20))
% 2.72/2.91          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 2.72/2.91      inference('cnf', [status(esa)], [t38_relset_1])).
% 2.72/2.91  thf('27', plain,
% 2.72/2.91      (((k8_relset_1 @ sk_B @ sk_C @ sk_E @ sk_C)
% 2.72/2.91         = (k1_relset_1 @ sk_B @ sk_C @ sk_E))),
% 2.72/2.91      inference('sup-', [status(thm)], ['25', '26'])).
% 2.72/2.91  thf('28', plain,
% 2.72/2.91      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf(redefinition_k8_relset_1, axiom,
% 2.72/2.91    (![A:$i,B:$i,C:$i,D:$i]:
% 2.72/2.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.72/2.91       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 2.72/2.91  thf('29', plain,
% 2.72/2.91      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 2.72/2.91         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 2.72/2.91          | ((k8_relset_1 @ X15 @ X16 @ X14 @ X17) = (k10_relat_1 @ X14 @ X17)))),
% 2.72/2.91      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 2.72/2.91  thf('30', plain,
% 2.72/2.91      (![X0 : $i]:
% 2.72/2.91         ((k8_relset_1 @ sk_B @ sk_C @ sk_E @ X0) = (k10_relat_1 @ sk_E @ X0))),
% 2.72/2.91      inference('sup-', [status(thm)], ['28', '29'])).
% 2.72/2.91  thf('31', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf(d1_funct_2, axiom,
% 2.72/2.91    (![A:$i,B:$i,C:$i]:
% 2.72/2.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.72/2.91       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.72/2.91           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.72/2.91             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.72/2.91         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.72/2.91           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.72/2.91             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.72/2.91  thf(zf_stmt_1, axiom,
% 2.72/2.91    (![C:$i,B:$i,A:$i]:
% 2.72/2.91     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.72/2.91       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.72/2.91  thf('32', plain,
% 2.72/2.91      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.72/2.91         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 2.72/2.91          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 2.72/2.91          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.72/2.91  thf('33', plain,
% 2.72/2.91      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 2.72/2.91        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 2.72/2.91      inference('sup-', [status(thm)], ['31', '32'])).
% 2.72/2.91  thf(zf_stmt_2, axiom,
% 2.72/2.91    (![B:$i,A:$i]:
% 2.72/2.91     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.72/2.91       ( zip_tseitin_0 @ B @ A ) ))).
% 2.72/2.91  thf('34', plain,
% 2.72/2.91      (![X21 : $i, X22 : $i]:
% 2.72/2.91         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.72/2.91  thf('35', plain,
% 2.72/2.91      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.72/2.91  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.72/2.91  thf(zf_stmt_5, axiom,
% 2.72/2.91    (![A:$i,B:$i,C:$i]:
% 2.72/2.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.72/2.91       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.72/2.91         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.72/2.91           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.72/2.91             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.72/2.91  thf('36', plain,
% 2.72/2.91      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.72/2.91         (~ (zip_tseitin_0 @ X26 @ X27)
% 2.72/2.91          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 2.72/2.91          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.72/2.91  thf('37', plain,
% 2.72/2.91      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 2.72/2.91      inference('sup-', [status(thm)], ['35', '36'])).
% 2.72/2.91  thf('38', plain,
% 2.72/2.91      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 2.72/2.91      inference('sup-', [status(thm)], ['34', '37'])).
% 2.72/2.91  thf('39', plain, (((sk_C) != (k1_xboole_0))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf('40', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 2.72/2.91      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 2.72/2.91  thf('41', plain, (((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E))),
% 2.72/2.91      inference('demod', [status(thm)], ['33', '40'])).
% 2.72/2.91  thf('42', plain, (((k10_relat_1 @ sk_E @ sk_C) = (sk_B))),
% 2.72/2.91      inference('demod', [status(thm)], ['27', '30', '41'])).
% 2.72/2.91  thf('43', plain,
% 2.72/2.91      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf('44', plain,
% 2.72/2.91      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.72/2.91         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 2.72/2.91          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 2.72/2.91      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.72/2.91  thf('45', plain,
% 2.72/2.91      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 2.72/2.91      inference('sup-', [status(thm)], ['43', '44'])).
% 2.72/2.91  thf('46', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_C))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf('47', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 2.72/2.91      inference('sup+', [status(thm)], ['45', '46'])).
% 2.72/2.91  thf(t169_relat_1, axiom,
% 2.72/2.91    (![A:$i]:
% 2.72/2.91     ( ( v1_relat_1 @ A ) =>
% 2.72/2.91       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 2.72/2.91  thf('48', plain,
% 2.72/2.91      (![X5 : $i]:
% 2.72/2.91         (((k10_relat_1 @ X5 @ (k2_relat_1 @ X5)) = (k1_relat_1 @ X5))
% 2.72/2.91          | ~ (v1_relat_1 @ X5))),
% 2.72/2.91      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.72/2.91  thf('49', plain,
% 2.72/2.91      ((((k10_relat_1 @ sk_E @ sk_C) = (k1_relat_1 @ sk_E))
% 2.72/2.91        | ~ (v1_relat_1 @ sk_E))),
% 2.72/2.91      inference('sup+', [status(thm)], ['47', '48'])).
% 2.72/2.91  thf('50', plain,
% 2.72/2.91      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf(cc1_relset_1, axiom,
% 2.72/2.91    (![A:$i,B:$i,C:$i]:
% 2.72/2.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.72/2.91       ( v1_relat_1 @ C ) ))).
% 2.72/2.91  thf('51', plain,
% 2.72/2.91      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.72/2.91         ((v1_relat_1 @ X8)
% 2.72/2.91          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 2.72/2.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.72/2.91  thf('52', plain, ((v1_relat_1 @ sk_E)),
% 2.72/2.91      inference('sup-', [status(thm)], ['50', '51'])).
% 2.72/2.91  thf('53', plain, (((k10_relat_1 @ sk_E @ sk_C) = (k1_relat_1 @ sk_E))),
% 2.72/2.91      inference('demod', [status(thm)], ['49', '52'])).
% 2.72/2.91  thf('54', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 2.72/2.91      inference('sup+', [status(thm)], ['42', '53'])).
% 2.72/2.91  thf(t47_relat_1, axiom,
% 2.72/2.91    (![A:$i]:
% 2.72/2.91     ( ( v1_relat_1 @ A ) =>
% 2.72/2.91       ( ![B:$i]:
% 2.72/2.91         ( ( v1_relat_1 @ B ) =>
% 2.72/2.91           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 2.72/2.91             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.72/2.91  thf('55', plain,
% 2.72/2.91      (![X6 : $i, X7 : $i]:
% 2.72/2.91         (~ (v1_relat_1 @ X6)
% 2.72/2.91          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X7)) = (k2_relat_1 @ X7))
% 2.72/2.91          | ~ (r1_tarski @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X6))
% 2.72/2.91          | ~ (v1_relat_1 @ X7))),
% 2.72/2.91      inference('cnf', [status(esa)], [t47_relat_1])).
% 2.72/2.91  thf('56', plain,
% 2.72/2.91      (![X0 : $i]:
% 2.72/2.91         (~ (r1_tarski @ sk_B @ (k2_relat_1 @ X0))
% 2.72/2.91          | ~ (v1_relat_1 @ sk_E)
% 2.72/2.91          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ sk_E)) = (k2_relat_1 @ sk_E))
% 2.72/2.91          | ~ (v1_relat_1 @ X0))),
% 2.72/2.91      inference('sup-', [status(thm)], ['54', '55'])).
% 2.72/2.91  thf('57', plain, ((v1_relat_1 @ sk_E)),
% 2.72/2.91      inference('sup-', [status(thm)], ['50', '51'])).
% 2.72/2.91  thf('58', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 2.72/2.91      inference('sup+', [status(thm)], ['45', '46'])).
% 2.72/2.91  thf('59', plain,
% 2.72/2.91      (![X0 : $i]:
% 2.72/2.91         (~ (r1_tarski @ sk_B @ (k2_relat_1 @ X0))
% 2.72/2.91          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ sk_E)) = (sk_C))
% 2.72/2.91          | ~ (v1_relat_1 @ X0))),
% 2.72/2.91      inference('demod', [status(thm)], ['56', '57', '58'])).
% 2.72/2.91  thf('60', plain,
% 2.72/2.91      ((~ (r1_tarski @ sk_B @ sk_B)
% 2.72/2.91        | ~ (v1_relat_1 @ sk_D)
% 2.72/2.91        | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C)))),
% 2.72/2.91      inference('sup-', [status(thm)], ['24', '59'])).
% 2.72/2.91  thf(dt_k2_subset_1, axiom,
% 2.72/2.91    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 2.72/2.91  thf('61', plain,
% 2.72/2.91      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 2.72/2.91      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 2.72/2.91  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 2.72/2.91  thf('62', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 2.72/2.91      inference('cnf', [status(esa)], [d4_subset_1])).
% 2.72/2.91  thf('63', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 2.72/2.91      inference('demod', [status(thm)], ['61', '62'])).
% 2.72/2.91  thf(t3_subset, axiom,
% 2.72/2.91    (![A:$i,B:$i]:
% 2.72/2.91     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.72/2.91  thf('64', plain,
% 2.72/2.91      (![X2 : $i, X3 : $i]:
% 2.72/2.91         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 2.72/2.91      inference('cnf', [status(esa)], [t3_subset])).
% 2.72/2.91  thf('65', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.72/2.91      inference('sup-', [status(thm)], ['63', '64'])).
% 2.72/2.91  thf('66', plain,
% 2.72/2.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf('67', plain,
% 2.72/2.91      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.72/2.91         ((v1_relat_1 @ X8)
% 2.72/2.91          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 2.72/2.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.72/2.91  thf('68', plain, ((v1_relat_1 @ sk_D)),
% 2.72/2.91      inference('sup-', [status(thm)], ['66', '67'])).
% 2.72/2.91  thf('69', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.72/2.91      inference('demod', [status(thm)], ['60', '65', '68'])).
% 2.72/2.91  thf('70', plain,
% 2.72/2.91      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.72/2.91      inference('demod', [status(thm)], ['19', '69'])).
% 2.72/2.91  thf('71', plain,
% 2.72/2.91      (((k2_relset_1 @ sk_A @ sk_C @ 
% 2.72/2.91         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) != (sk_C))),
% 2.72/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.91  thf('72', plain,
% 2.72/2.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.72/2.91         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.72/2.91      inference('demod', [status(thm)], ['14', '15'])).
% 2.72/2.91  thf('73', plain,
% 2.72/2.91      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 2.72/2.91      inference('demod', [status(thm)], ['71', '72'])).
% 2.72/2.91  thf('74', plain, ($false),
% 2.72/2.91      inference('simplify_reflect-', [status(thm)], ['70', '73'])).
% 2.72/2.91  
% 2.72/2.91  % SZS output end Refutation
% 2.72/2.91  
% 2.76/2.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
