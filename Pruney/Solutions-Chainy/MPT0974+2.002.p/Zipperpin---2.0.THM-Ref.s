%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mt4yAirpjt

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:40 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 180 expanded)
%              Number of leaves         :   38 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  913 (3789 expanded)
%              Number of equality atoms :   57 ( 276 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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

thf('26',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('31',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('37',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['27','34','37'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X2 @ X3 ) )
        = ( k2_relat_1 @ X3 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        = ( k2_relat_1 @ sk_E ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('42',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('43',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        = sk_C )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','43','48'])).

thf('50',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['24','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v5_relat_1 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('58',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['22','23'])).

thf('61',plain,(
    r1_tarski @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf('63',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['50','61','62'])).

thf('64',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['19','63'])).

thf('65',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('67',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mt4yAirpjt
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:32:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.05/1.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.05/1.24  % Solved by: fo/fo7.sh
% 1.05/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.24  % done 649 iterations in 0.792s
% 1.05/1.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.05/1.24  % SZS output start Refutation
% 1.05/1.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.05/1.24  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.05/1.24  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.05/1.24  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.24  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.05/1.24  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.05/1.24  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.05/1.24  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.05/1.24  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.05/1.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.24  thf(sk_D_type, type, sk_D: $i).
% 1.05/1.24  thf(sk_C_type, type, sk_C: $i).
% 1.05/1.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.24  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.05/1.24  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.05/1.24  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.05/1.24  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.05/1.24  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.05/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.24  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.05/1.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.24  thf(sk_E_type, type, sk_E: $i).
% 1.05/1.24  thf(t20_funct_2, conjecture,
% 1.05/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.24     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.05/1.24         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.24       ( ![E:$i]:
% 1.05/1.24         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.05/1.24             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.05/1.24           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.05/1.24               ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 1.05/1.24             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.05/1.24               ( ( k2_relset_1 @
% 1.05/1.24                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.05/1.24                 ( C ) ) ) ) ) ) ))).
% 1.05/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.24    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.24        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.05/1.24            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.24          ( ![E:$i]:
% 1.05/1.24            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.05/1.24                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.05/1.24              ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.05/1.24                  ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 1.05/1.24                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.05/1.24                  ( ( k2_relset_1 @
% 1.05/1.24                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.05/1.24                    ( C ) ) ) ) ) ) ) )),
% 1.05/1.24    inference('cnf.neg', [status(esa)], [t20_funct_2])).
% 1.05/1.24  thf('0', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('1', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(dt_k1_partfun1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.05/1.24     ( ( ( v1_funct_1 @ E ) & 
% 1.05/1.24         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.05/1.24         ( v1_funct_1 @ F ) & 
% 1.05/1.24         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.05/1.24       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.05/1.24         ( m1_subset_1 @
% 1.05/1.24           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.05/1.24           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.05/1.24  thf('2', plain,
% 1.05/1.24      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.05/1.24          | ~ (v1_funct_1 @ X24)
% 1.05/1.24          | ~ (v1_funct_1 @ X27)
% 1.05/1.24          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.05/1.24          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 1.05/1.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 1.05/1.24      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.05/1.24  thf('3', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.24         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.05/1.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.05/1.24          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.05/1.24          | ~ (v1_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_funct_1 @ sk_D))),
% 1.05/1.24      inference('sup-', [status(thm)], ['1', '2'])).
% 1.05/1.24  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('5', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.24         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.05/1.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.05/1.24          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.05/1.24          | ~ (v1_funct_1 @ X1))),
% 1.05/1.24      inference('demod', [status(thm)], ['3', '4'])).
% 1.05/1.24  thf('6', plain,
% 1.05/1.24      ((~ (v1_funct_1 @ sk_E)
% 1.05/1.24        | (m1_subset_1 @ 
% 1.05/1.24           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 1.05/1.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.05/1.24      inference('sup-', [status(thm)], ['0', '5'])).
% 1.05/1.24  thf('7', plain, ((v1_funct_1 @ sk_E)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('8', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('9', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(redefinition_k1_partfun1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.05/1.24     ( ( ( v1_funct_1 @ E ) & 
% 1.05/1.24         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.05/1.24         ( v1_funct_1 @ F ) & 
% 1.05/1.24         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.05/1.24       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.05/1.24  thf('10', plain,
% 1.05/1.24      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.05/1.24          | ~ (v1_funct_1 @ X30)
% 1.05/1.24          | ~ (v1_funct_1 @ X33)
% 1.05/1.24          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.05/1.24          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 1.05/1.24              = (k5_relat_1 @ X30 @ X33)))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.05/1.24  thf('11', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.24         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.05/1.24            = (k5_relat_1 @ sk_D @ X0))
% 1.05/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.05/1.24          | ~ (v1_funct_1 @ X0)
% 1.05/1.24          | ~ (v1_funct_1 @ sk_D))),
% 1.05/1.24      inference('sup-', [status(thm)], ['9', '10'])).
% 1.05/1.24  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('13', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.24         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.05/1.24            = (k5_relat_1 @ sk_D @ X0))
% 1.05/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.05/1.24          | ~ (v1_funct_1 @ X0))),
% 1.05/1.24      inference('demod', [status(thm)], ['11', '12'])).
% 1.05/1.24  thf('14', plain,
% 1.05/1.24      ((~ (v1_funct_1 @ sk_E)
% 1.05/1.24        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.05/1.24            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['8', '13'])).
% 1.05/1.24  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('16', plain,
% 1.05/1.24      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.05/1.24         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.05/1.24      inference('demod', [status(thm)], ['14', '15'])).
% 1.05/1.24  thf('17', plain,
% 1.05/1.24      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 1.05/1.24        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.05/1.24      inference('demod', [status(thm)], ['6', '7', '16'])).
% 1.05/1.24  thf(redefinition_k2_relset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.24       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.05/1.24  thf('18', plain,
% 1.05/1.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.05/1.24         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 1.05/1.24          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.05/1.24  thf('19', plain,
% 1.05/1.24      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 1.05/1.24         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['17', '18'])).
% 1.05/1.24  thf('20', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('21', plain,
% 1.05/1.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.05/1.24         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 1.05/1.24          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.05/1.24  thf('22', plain,
% 1.05/1.24      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.05/1.24      inference('sup-', [status(thm)], ['20', '21'])).
% 1.05/1.24  thf('23', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_B))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('24', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 1.05/1.24      inference('sup+', [status(thm)], ['22', '23'])).
% 1.05/1.24  thf('25', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(d1_funct_2, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.24       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.05/1.24           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.05/1.24             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.05/1.24         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.05/1.24           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.05/1.24             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.05/1.24  thf(zf_stmt_1, axiom,
% 1.05/1.24    (![C:$i,B:$i,A:$i]:
% 1.05/1.24     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.05/1.24       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.05/1.24  thf('26', plain,
% 1.05/1.24      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.05/1.24         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 1.05/1.24          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 1.05/1.24          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.05/1.24  thf('27', plain,
% 1.05/1.24      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.05/1.24        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['25', '26'])).
% 1.05/1.24  thf(zf_stmt_2, axiom,
% 1.05/1.24    (![B:$i,A:$i]:
% 1.05/1.24     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.05/1.24       ( zip_tseitin_0 @ B @ A ) ))).
% 1.05/1.24  thf('28', plain,
% 1.05/1.24      (![X16 : $i, X17 : $i]:
% 1.05/1.24         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.05/1.24  thf('29', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.05/1.24  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.05/1.24  thf(zf_stmt_5, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.24       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.05/1.24         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.05/1.24           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.05/1.24             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.05/1.24  thf('30', plain,
% 1.05/1.24      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.05/1.24         (~ (zip_tseitin_0 @ X21 @ X22)
% 1.05/1.24          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 1.05/1.24          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.05/1.24  thf('31', plain,
% 1.05/1.24      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.05/1.24      inference('sup-', [status(thm)], ['29', '30'])).
% 1.05/1.24  thf('32', plain,
% 1.05/1.24      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 1.05/1.24      inference('sup-', [status(thm)], ['28', '31'])).
% 1.05/1.24  thf('33', plain, (((sk_C) != (k1_xboole_0))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('34', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 1.05/1.24      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 1.05/1.24  thf('35', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(redefinition_k1_relset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.24       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.05/1.24  thf('36', plain,
% 1.05/1.24      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.05/1.24         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 1.05/1.24          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.05/1.24  thf('37', plain,
% 1.05/1.24      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.05/1.24      inference('sup-', [status(thm)], ['35', '36'])).
% 1.05/1.24  thf('38', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 1.05/1.24      inference('demod', [status(thm)], ['27', '34', '37'])).
% 1.05/1.24  thf(t47_relat_1, axiom,
% 1.05/1.24    (![A:$i]:
% 1.05/1.24     ( ( v1_relat_1 @ A ) =>
% 1.05/1.24       ( ![B:$i]:
% 1.05/1.24         ( ( v1_relat_1 @ B ) =>
% 1.05/1.24           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 1.05/1.24             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.05/1.24  thf('39', plain,
% 1.05/1.24      (![X2 : $i, X3 : $i]:
% 1.05/1.24         (~ (v1_relat_1 @ X2)
% 1.05/1.24          | ((k2_relat_1 @ (k5_relat_1 @ X2 @ X3)) = (k2_relat_1 @ X3))
% 1.05/1.24          | ~ (r1_tarski @ (k1_relat_1 @ X3) @ (k2_relat_1 @ X2))
% 1.05/1.24          | ~ (v1_relat_1 @ X3))),
% 1.05/1.24      inference('cnf', [status(esa)], [t47_relat_1])).
% 1.05/1.24  thf('40', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (~ (r1_tarski @ sk_B @ (k2_relat_1 @ X0))
% 1.05/1.24          | ~ (v1_relat_1 @ sk_E)
% 1.05/1.24          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ sk_E)) = (k2_relat_1 @ sk_E))
% 1.05/1.24          | ~ (v1_relat_1 @ X0))),
% 1.05/1.24      inference('sup-', [status(thm)], ['38', '39'])).
% 1.05/1.24  thf('41', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(cc1_relset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.24       ( v1_relat_1 @ C ) ))).
% 1.05/1.24  thf('42', plain,
% 1.05/1.24      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.05/1.24         ((v1_relat_1 @ X4)
% 1.05/1.24          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.05/1.24      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.05/1.24  thf('43', plain, ((v1_relat_1 @ sk_E)),
% 1.05/1.24      inference('sup-', [status(thm)], ['41', '42'])).
% 1.05/1.24  thf('44', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('45', plain,
% 1.05/1.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.05/1.24         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 1.05/1.24          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.05/1.24  thf('46', plain,
% 1.05/1.24      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 1.05/1.24      inference('sup-', [status(thm)], ['44', '45'])).
% 1.05/1.24  thf('47', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_C))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('48', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 1.05/1.24      inference('sup+', [status(thm)], ['46', '47'])).
% 1.05/1.24  thf('49', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (~ (r1_tarski @ sk_B @ (k2_relat_1 @ X0))
% 1.05/1.24          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ sk_E)) = (sk_C))
% 1.05/1.24          | ~ (v1_relat_1 @ X0))),
% 1.05/1.24      inference('demod', [status(thm)], ['40', '43', '48'])).
% 1.05/1.24  thf('50', plain,
% 1.05/1.24      ((~ (r1_tarski @ sk_B @ sk_B)
% 1.05/1.24        | ~ (v1_relat_1 @ sk_D)
% 1.05/1.24        | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['24', '49'])).
% 1.05/1.24  thf('51', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(cc2_relset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.24       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.05/1.24  thf('52', plain,
% 1.05/1.24      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.05/1.24         ((v5_relat_1 @ X7 @ X9)
% 1.05/1.24          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.05/1.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.05/1.24  thf('53', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 1.05/1.24      inference('sup-', [status(thm)], ['51', '52'])).
% 1.05/1.24  thf(d19_relat_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( v1_relat_1 @ B ) =>
% 1.05/1.24       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.05/1.24  thf('54', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         (~ (v5_relat_1 @ X0 @ X1)
% 1.05/1.24          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ X0))),
% 1.05/1.24      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.05/1.24  thf('55', plain,
% 1.05/1.24      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 1.05/1.24      inference('sup-', [status(thm)], ['53', '54'])).
% 1.05/1.24  thf('56', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('57', plain,
% 1.05/1.24      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.05/1.24         ((v1_relat_1 @ X4)
% 1.05/1.24          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.05/1.24      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.05/1.24  thf('58', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.24      inference('sup-', [status(thm)], ['56', '57'])).
% 1.05/1.24  thf('59', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 1.05/1.24      inference('demod', [status(thm)], ['55', '58'])).
% 1.05/1.24  thf('60', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 1.05/1.24      inference('sup+', [status(thm)], ['22', '23'])).
% 1.05/1.24  thf('61', plain, ((r1_tarski @ sk_B @ sk_B)),
% 1.05/1.24      inference('demod', [status(thm)], ['59', '60'])).
% 1.05/1.24  thf('62', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.24      inference('sup-', [status(thm)], ['56', '57'])).
% 1.05/1.24  thf('63', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.05/1.24      inference('demod', [status(thm)], ['50', '61', '62'])).
% 1.05/1.24  thf('64', plain,
% 1.05/1.24      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.05/1.24      inference('demod', [status(thm)], ['19', '63'])).
% 1.05/1.24  thf('65', plain,
% 1.05/1.24      (((k2_relset_1 @ sk_A @ sk_C @ 
% 1.05/1.24         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) != (sk_C))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('66', plain,
% 1.05/1.24      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.05/1.24         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.05/1.24      inference('demod', [status(thm)], ['14', '15'])).
% 1.05/1.24  thf('67', plain,
% 1.05/1.24      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 1.05/1.24      inference('demod', [status(thm)], ['65', '66'])).
% 1.05/1.24  thf('68', plain, ($false),
% 1.05/1.24      inference('simplify_reflect-', [status(thm)], ['64', '67'])).
% 1.05/1.24  
% 1.05/1.24  % SZS output end Refutation
% 1.05/1.24  
% 1.05/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
