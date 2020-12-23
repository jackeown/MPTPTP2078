%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vQp0Up1R4N

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:23 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  144 (1478 expanded)
%              Number of leaves         :   44 ( 434 expanded)
%              Depth                    :   35
%              Number of atoms          : 1282 (25003 expanded)
%              Number of equality atoms :   97 ( 959 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t191_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ~ ( v1_xboole_0 @ C )
         => ! [D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ B @ C )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
             => ( ! [E: $i] :
                    ( ( m1_subset_1 @ E @ B )
                   => ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) )
               => ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( v1_xboole_0 @ B )
       => ! [C: $i] :
            ( ~ ( v1_xboole_0 @ C )
           => ! [D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ B @ C )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
               => ( ! [E: $i] :
                      ( ( m1_subset_1 @ E @ B )
                     => ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) )
                 => ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t191_funct_2])).

thf('3',plain,(
    ! [X48: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ X48 ) @ sk_A )
      | ~ ( m1_subset_1 @ X48 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r2_hidden @ ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X33 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X33 ) ) )
      | ( r2_hidden @ X32 @ ( k1_funct_2 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t11_funct_2])).

thf('11',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_funct_2 @ sk_B_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_funct_2 @ sk_B_1 @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(d2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E )
              & ( D = E )
              & ( ( k1_relat_1 @ E )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X24 @ X21 @ X22 ) @ X24 @ X21 @ X22 )
      | ( X23
       != ( k1_funct_2 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X24 @ X21 @ X22 ) @ X24 @ X21 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_funct_2 @ X22 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_E_1 @ sk_D_3 @ sk_C @ sk_B_1 ) @ sk_D_3 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X16 = X14 )
      | ~ ( zip_tseitin_0 @ X14 @ X16 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_3
      = ( sk_E_1 @ sk_D_3 @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_E_1 @ sk_D_3 @ sk_C @ sk_B_1 ) @ sk_D_3 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ X14 )
        = X17 )
      | ~ ( zip_tseitin_0 @ X14 @ X16 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ ( sk_E_1 @ sk_D_3 @ sk_C @ sk_B_1 ) )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k1_relat_1 @ sk_D_3 )
      = sk_B_1 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_3 )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_3 )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('26',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_3 )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('27',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( zip_tseitin_1 @ X38 @ X39 @ X40 @ X41 )
      | ( r2_hidden @ X38 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_1 @ D @ C @ B @ A ) )
       => ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( ( k1_relat_1 @ X46 )
       != X45 )
      | ~ ( zip_tseitin_1 @ ( sk_D_2 @ X46 @ X47 @ X45 ) @ X46 @ X47 @ X45 )
      | ( zip_tseitin_2 @ X46 @ X47 @ X45 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('29',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ~ ( v1_funct_1 @ X46 )
      | ( zip_tseitin_2 @ X46 @ X47 @ ( k1_relat_1 @ X46 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_2 @ X46 @ X47 @ ( k1_relat_1 @ X46 ) ) @ X46 @ X47 @ ( k1_relat_1 @ X46 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_2 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_D_3 ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ( zip_tseitin_2 @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_D_3 ) )
      | ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_2 @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) ) ) ),
    inference(demod,[status(thm)],['31','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B_1 ) @ sk_B_1 )
      | ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_2 @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
      | ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_2 @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('42',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ X28 )
      | ( ( k3_funct_2 @ X28 @ X29 @ X27 @ X30 )
        = ( k1_funct_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ X0 )
        = ( k1_funct_1 @ sk_D_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ X0 )
        = ( k1_funct_1 @ sk_D_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ X0 )
        = ( k1_funct_1 @ sk_D_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
      | ( sk_C = k1_xboole_0 )
      | ( ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B_1 ) )
        = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_2 @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('51',plain,(
    ! [X48: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ X48 ) @ sk_A )
      | ~ ( m1_subset_1 @ X48 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
      | ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B_1 ) ) @ sk_A )
      | ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_2 @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
      | ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_2 @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
      | ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B_1 ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( zip_tseitin_1 @ X38 @ X39 @ X40 @ X41 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X39 @ X38 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_2 @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
      | ( zip_tseitin_1 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B_1 ) @ sk_D_3 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_3 )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('58',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ~ ( v1_funct_1 @ X46 )
      | ( zip_tseitin_2 @ X46 @ X47 @ ( k1_relat_1 @ X46 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_2 @ X46 @ X47 @ ( k1_relat_1 @ X46 ) ) @ X46 @ X47 @ ( k1_relat_1 @ X46 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B_1 ) @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
      | ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_2 @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B_1 ) @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
      | ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_2 @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( zip_tseitin_2 @ sk_D_3 @ sk_A @ ( k1_relat_1 @ sk_D_3 ) )
    | ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_3 @ sk_A @ ( k1_relat_1 @ sk_D_3 ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_3 @ sk_A @ ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( zip_tseitin_2 @ sk_D_3 @ sk_A @ sk_B_1 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','64'])).

thf('66',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_3 @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( v1_funct_2 @ X42 @ X44 @ X43 )
      | ~ ( zip_tseitin_2 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('68',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_3 @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('70',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( zip_tseitin_2 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('71',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X33 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X33 ) ) )
      | ( r2_hidden @ X32 @ ( k1_funct_2 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t11_funct_2])).

thf('73',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ sk_D_3 @ ( k1_funct_2 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ sk_D_3 @ ( k1_funct_2 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ sk_D_3 @ ( k1_funct_2 @ sk_B_1 @ sk_A ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_funct_2 @ sk_B_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X24 @ X21 @ X22 ) @ X24 @ X21 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_funct_2 @ X22 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('79',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_E_1 @ sk_D_3 @ sk_A @ sk_B_1 ) @ sk_D_3 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X16 = X14 )
      | ~ ( zip_tseitin_0 @ X14 @ X16 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D_3
      = ( sk_E_1 @ sk_D_3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_E_1 @ sk_D_3 @ sk_A @ sk_B_1 ) @ sk_D_3 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('83',plain,
    ( ( zip_tseitin_0 @ sk_D_3 @ sk_D_3 @ sk_A @ sk_B_1 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_0 @ sk_D_3 @ sk_D_3 @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( zip_tseitin_0 @ X14 @ X16 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('86',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_3 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('89',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('90',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ sk_A ) ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['86','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('95',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('96',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['8','96','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vQp0Up1R4N
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 465 iterations in 0.247s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.68  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.45/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.68  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.45/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.68  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.45/0.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.45/0.68  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.45/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.68  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.45/0.68  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.45/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.68  thf(d1_xboole_0, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.68  thf('0', plain,
% 0.45/0.68      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.45/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.68  thf(t1_subset, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.45/0.68  thf('1', plain,
% 0.45/0.68      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [t1_subset])).
% 0.45/0.68  thf('2', plain,
% 0.45/0.68      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.68  thf(t191_funct_2, conjecture,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.68       ( ![C:$i]:
% 0.45/0.68         ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.45/0.68           ( ![D:$i]:
% 0.45/0.68             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.45/0.68                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.45/0.68               ( ( ![E:$i]:
% 0.45/0.68                   ( ( m1_subset_1 @ E @ B ) =>
% 0.45/0.68                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.45/0.68                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.68    (~( ![A:$i,B:$i]:
% 0.45/0.68        ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.68          ( ![C:$i]:
% 0.45/0.68            ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.45/0.68              ( ![D:$i]:
% 0.45/0.68                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.45/0.68                    ( m1_subset_1 @
% 0.45/0.68                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.45/0.68                  ( ( ![E:$i]:
% 0.45/0.68                      ( ( m1_subset_1 @ E @ B ) =>
% 0.45/0.68                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.45/0.68                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 0.45/0.68    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 0.45/0.68  thf('3', plain,
% 0.45/0.68      (![X48 : $i]:
% 0.45/0.68         ((r2_hidden @ (k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ X48) @ sk_A)
% 0.45/0.68          | ~ (m1_subset_1 @ X48 @ sk_B_1))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('4', plain,
% 0.45/0.68      (((v1_xboole_0 @ sk_B_1)
% 0.45/0.68        | (r2_hidden @ 
% 0.45/0.68           (k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.68  thf('5', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('6', plain,
% 0.45/0.68      ((r2_hidden @ (k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ (sk_B @ sk_B_1)) @ 
% 0.45/0.68        sk_A)),
% 0.45/0.68      inference('clc', [status(thm)], ['4', '5'])).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.68  thf('8', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.45/0.68      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.68  thf('9', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(t11_funct_2, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.68       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.68         ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ))).
% 0.45/0.68  thf('10', plain,
% 0.45/0.68      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.68         (((X33) = (k1_xboole_0))
% 0.45/0.68          | ~ (v1_funct_1 @ X32)
% 0.45/0.68          | ~ (v1_funct_2 @ X32 @ X31 @ X33)
% 0.45/0.68          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X33)))
% 0.45/0.68          | (r2_hidden @ X32 @ (k1_funct_2 @ X31 @ X33)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t11_funct_2])).
% 0.45/0.69  thf('11', plain,
% 0.45/0.69      (((r2_hidden @ sk_D_3 @ (k1_funct_2 @ sk_B_1 @ sk_C))
% 0.45/0.69        | ~ (v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C)
% 0.45/0.69        | ~ (v1_funct_1 @ sk_D_3)
% 0.45/0.69        | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.69  thf('12', plain, ((v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('13', plain, ((v1_funct_1 @ sk_D_3)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('14', plain,
% 0.45/0.69      (((r2_hidden @ sk_D_3 @ (k1_funct_2 @ sk_B_1 @ sk_C))
% 0.45/0.69        | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.45/0.69  thf(d2_funct_2, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.45/0.69       ( ![D:$i]:
% 0.45/0.69         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.69           ( ?[E:$i]:
% 0.45/0.69             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.45/0.69               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.45/0.69               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.45/0.69  thf(zf_stmt_2, axiom,
% 0.45/0.69    (![E:$i,D:$i,B:$i,A:$i]:
% 0.45/0.69     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.45/0.69       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.45/0.69         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.45/0.69         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.45/0.69  thf(zf_stmt_3, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.45/0.69       ( ![D:$i]:
% 0.45/0.69         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.69           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 0.45/0.69  thf('15', plain,
% 0.45/0.69      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X24 @ X23)
% 0.45/0.69          | (zip_tseitin_0 @ (sk_E_1 @ X24 @ X21 @ X22) @ X24 @ X21 @ X22)
% 0.45/0.69          | ((X23) != (k1_funct_2 @ X22 @ X21)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.69  thf('16', plain,
% 0.45/0.69      (![X21 : $i, X22 : $i, X24 : $i]:
% 0.45/0.69         ((zip_tseitin_0 @ (sk_E_1 @ X24 @ X21 @ X22) @ X24 @ X21 @ X22)
% 0.45/0.69          | ~ (r2_hidden @ X24 @ (k1_funct_2 @ X22 @ X21)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['15'])).
% 0.45/0.69  thf('17', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0))
% 0.45/0.69        | (zip_tseitin_0 @ (sk_E_1 @ sk_D_3 @ sk_C @ sk_B_1) @ sk_D_3 @ sk_C @ 
% 0.45/0.69           sk_B_1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['14', '16'])).
% 0.45/0.69  thf('18', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.69         (((X16) = (X14)) | ~ (zip_tseitin_0 @ X14 @ X16 @ X15 @ X17))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.69  thf('19', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0))
% 0.45/0.69        | ((sk_D_3) = (sk_E_1 @ sk_D_3 @ sk_C @ sk_B_1)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.69  thf('20', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0))
% 0.45/0.69        | (zip_tseitin_0 @ (sk_E_1 @ sk_D_3 @ sk_C @ sk_B_1) @ sk_D_3 @ sk_C @ 
% 0.45/0.69           sk_B_1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['14', '16'])).
% 0.45/0.69  thf('21', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.69         (((k1_relat_1 @ X14) = (X17))
% 0.45/0.69          | ~ (zip_tseitin_0 @ X14 @ X16 @ X15 @ X17))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.69  thf('22', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0))
% 0.45/0.69        | ((k1_relat_1 @ (sk_E_1 @ sk_D_3 @ sk_C @ sk_B_1)) = (sk_B_1)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.69  thf('23', plain,
% 0.45/0.69      ((((k1_relat_1 @ sk_D_3) = (sk_B_1))
% 0.45/0.69        | ((sk_C) = (k1_xboole_0))
% 0.45/0.69        | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['19', '22'])).
% 0.45/0.69  thf('24', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0)) | ((k1_relat_1 @ sk_D_3) = (sk_B_1)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.69  thf('25', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0)) | ((k1_relat_1 @ sk_D_3) = (sk_B_1)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.69  thf('26', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0)) | ((k1_relat_1 @ sk_D_3) = (sk_B_1)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.69  thf(t5_funct_2, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.45/0.69       ( ( ( ![D:$i]:
% 0.45/0.69             ( ( r2_hidden @ D @ A ) =>
% 0.45/0.69               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.45/0.69           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.45/0.69         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.69           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_4, axiom,
% 0.45/0.69    (![D:$i,C:$i,B:$i,A:$i]:
% 0.45/0.69     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.45/0.69       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.45/0.69  thf('27', plain,
% 0.45/0.69      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.45/0.69         ((zip_tseitin_1 @ X38 @ X39 @ X40 @ X41) | (r2_hidden @ X38 @ X41))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.45/0.69  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.45/0.69  thf(zf_stmt_6, axiom,
% 0.45/0.69    (![C:$i,B:$i,A:$i]:
% 0.45/0.69     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.45/0.69       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_7, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.45/0.69  thf(zf_stmt_8, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.69       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.45/0.69           ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.45/0.69         ( zip_tseitin_2 @ C @ B @ A ) ) ))).
% 0.45/0.69  thf('28', plain,
% 0.45/0.69      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.45/0.69         (((k1_relat_1 @ X46) != (X45))
% 0.45/0.69          | ~ (zip_tseitin_1 @ (sk_D_2 @ X46 @ X47 @ X45) @ X46 @ X47 @ X45)
% 0.45/0.69          | (zip_tseitin_2 @ X46 @ X47 @ X45)
% 0.45/0.69          | ~ (v1_funct_1 @ X46)
% 0.45/0.69          | ~ (v1_relat_1 @ X46))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.45/0.69  thf('29', plain,
% 0.45/0.69      (![X46 : $i, X47 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X46)
% 0.45/0.69          | ~ (v1_funct_1 @ X46)
% 0.45/0.69          | (zip_tseitin_2 @ X46 @ X47 @ (k1_relat_1 @ X46))
% 0.45/0.69          | ~ (zip_tseitin_1 @ (sk_D_2 @ X46 @ X47 @ (k1_relat_1 @ X46)) @ 
% 0.45/0.69               X46 @ X47 @ (k1_relat_1 @ X46)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['28'])).
% 0.45/0.69  thf('30', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r2_hidden @ (sk_D_2 @ X0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.45/0.69           (k1_relat_1 @ X0))
% 0.45/0.69          | (zip_tseitin_2 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 0.45/0.69          | ~ (v1_funct_1 @ X0)
% 0.45/0.69          | ~ (v1_relat_1 @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['27', '29'])).
% 0.45/0.69  thf('31', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r2_hidden @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B_1) @ (k1_relat_1 @ sk_D_3))
% 0.45/0.69          | ((sk_C) = (k1_xboole_0))
% 0.45/0.69          | ~ (v1_relat_1 @ sk_D_3)
% 0.45/0.69          | ~ (v1_funct_1 @ sk_D_3)
% 0.45/0.69          | (zip_tseitin_2 @ sk_D_3 @ X0 @ (k1_relat_1 @ sk_D_3)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['26', '30'])).
% 0.45/0.69  thf('32', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(cc1_relset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( v1_relat_1 @ C ) ))).
% 0.45/0.69  thf('33', plain,
% 0.45/0.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.69         ((v1_relat_1 @ X8)
% 0.45/0.69          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.45/0.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.69  thf('34', plain, ((v1_relat_1 @ sk_D_3)),
% 0.45/0.69      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.69  thf('35', plain, ((v1_funct_1 @ sk_D_3)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('36', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r2_hidden @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B_1) @ (k1_relat_1 @ sk_D_3))
% 0.45/0.69          | ((sk_C) = (k1_xboole_0))
% 0.45/0.69          | (zip_tseitin_2 @ sk_D_3 @ X0 @ (k1_relat_1 @ sk_D_3)))),
% 0.45/0.69      inference('demod', [status(thm)], ['31', '34', '35'])).
% 0.45/0.69  thf('37', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r2_hidden @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B_1) @ sk_B_1)
% 0.45/0.69          | ((sk_C) = (k1_xboole_0))
% 0.45/0.69          | (zip_tseitin_2 @ sk_D_3 @ X0 @ (k1_relat_1 @ sk_D_3))
% 0.45/0.69          | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['25', '36'])).
% 0.45/0.69  thf('38', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((zip_tseitin_2 @ sk_D_3 @ X0 @ (k1_relat_1 @ sk_D_3))
% 0.45/0.69          | ((sk_C) = (k1_xboole_0))
% 0.45/0.69          | (r2_hidden @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B_1) @ sk_B_1))),
% 0.45/0.69      inference('simplify', [status(thm)], ['37'])).
% 0.45/0.69  thf('39', plain,
% 0.45/0.69      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_subset])).
% 0.45/0.69  thf('40', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((sk_C) = (k1_xboole_0))
% 0.45/0.69          | (zip_tseitin_2 @ sk_D_3 @ X0 @ (k1_relat_1 @ sk_D_3))
% 0.45/0.69          | (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B_1) @ sk_B_1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.69  thf('41', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(redefinition_k3_funct_2, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.69     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.45/0.69         ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.69         ( m1_subset_1 @ D @ A ) ) =>
% 0.45/0.69       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.45/0.69  thf('42', plain,
% 0.45/0.69      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.45/0.69          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.45/0.69          | ~ (v1_funct_1 @ X27)
% 0.45/0.69          | (v1_xboole_0 @ X28)
% 0.45/0.69          | ~ (m1_subset_1 @ X30 @ X28)
% 0.45/0.69          | ((k3_funct_2 @ X28 @ X29 @ X27 @ X30) = (k1_funct_1 @ X27 @ X30)))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.45/0.69  thf('43', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ X0)
% 0.45/0.69            = (k1_funct_1 @ sk_D_3 @ X0))
% 0.45/0.69          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.45/0.69          | (v1_xboole_0 @ sk_B_1)
% 0.45/0.69          | ~ (v1_funct_1 @ sk_D_3)
% 0.45/0.69          | ~ (v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.69  thf('44', plain, ((v1_funct_1 @ sk_D_3)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('45', plain, ((v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('46', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ X0)
% 0.45/0.69            = (k1_funct_1 @ sk_D_3 @ X0))
% 0.45/0.69          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.45/0.69          | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.69      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.45/0.69  thf('47', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('48', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.45/0.69          | ((k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ X0)
% 0.45/0.69              = (k1_funct_1 @ sk_D_3 @ X0)))),
% 0.45/0.69      inference('clc', [status(thm)], ['46', '47'])).
% 0.45/0.69  thf('49', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((zip_tseitin_2 @ sk_D_3 @ X0 @ (k1_relat_1 @ sk_D_3))
% 0.45/0.69          | ((sk_C) = (k1_xboole_0))
% 0.45/0.69          | ((k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ 
% 0.45/0.69              (sk_D_2 @ sk_D_3 @ X0 @ sk_B_1))
% 0.45/0.69              = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B_1))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['40', '48'])).
% 0.45/0.69  thf('50', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((sk_C) = (k1_xboole_0))
% 0.45/0.69          | (zip_tseitin_2 @ sk_D_3 @ X0 @ (k1_relat_1 @ sk_D_3))
% 0.45/0.69          | (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B_1) @ sk_B_1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.69  thf('51', plain,
% 0.45/0.69      (![X48 : $i]:
% 0.45/0.69         ((r2_hidden @ (k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ X48) @ sk_A)
% 0.45/0.69          | ~ (m1_subset_1 @ X48 @ sk_B_1))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('52', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((zip_tseitin_2 @ sk_D_3 @ X0 @ (k1_relat_1 @ sk_D_3))
% 0.45/0.69          | ((sk_C) = (k1_xboole_0))
% 0.45/0.69          | (r2_hidden @ 
% 0.45/0.69             (k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_3 @ 
% 0.45/0.69              (sk_D_2 @ sk_D_3 @ X0 @ sk_B_1)) @ 
% 0.45/0.69             sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.69  thf('53', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r2_hidden @ 
% 0.45/0.69           (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B_1)) @ sk_A)
% 0.45/0.69          | ((sk_C) = (k1_xboole_0))
% 0.45/0.69          | (zip_tseitin_2 @ sk_D_3 @ X0 @ (k1_relat_1 @ sk_D_3))
% 0.45/0.69          | ((sk_C) = (k1_xboole_0))
% 0.45/0.69          | (zip_tseitin_2 @ sk_D_3 @ X0 @ (k1_relat_1 @ sk_D_3)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['49', '52'])).
% 0.45/0.69  thf('54', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((zip_tseitin_2 @ sk_D_3 @ X0 @ (k1_relat_1 @ sk_D_3))
% 0.45/0.69          | ((sk_C) = (k1_xboole_0))
% 0.45/0.69          | (r2_hidden @ 
% 0.45/0.69             (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B_1)) @ sk_A))),
% 0.45/0.69      inference('simplify', [status(thm)], ['53'])).
% 0.45/0.69  thf('55', plain,
% 0.45/0.69      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.45/0.69         ((zip_tseitin_1 @ X38 @ X39 @ X40 @ X41)
% 0.45/0.69          | ~ (r2_hidden @ (k1_funct_1 @ X39 @ X38) @ X40))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.45/0.69  thf('56', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((sk_C) = (k1_xboole_0))
% 0.45/0.69          | (zip_tseitin_2 @ sk_D_3 @ X0 @ (k1_relat_1 @ sk_D_3))
% 0.45/0.69          | (zip_tseitin_1 @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B_1) @ sk_D_3 @ sk_A @ 
% 0.45/0.69             X1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['54', '55'])).
% 0.45/0.69  thf('57', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0)) | ((k1_relat_1 @ sk_D_3) = (sk_B_1)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.69  thf('58', plain,
% 0.45/0.69      (![X46 : $i, X47 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X46)
% 0.45/0.69          | ~ (v1_funct_1 @ X46)
% 0.45/0.69          | (zip_tseitin_2 @ X46 @ X47 @ (k1_relat_1 @ X46))
% 0.45/0.69          | ~ (zip_tseitin_1 @ (sk_D_2 @ X46 @ X47 @ (k1_relat_1 @ X46)) @ 
% 0.45/0.69               X46 @ X47 @ (k1_relat_1 @ X46)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['28'])).
% 0.45/0.69  thf('59', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (zip_tseitin_1 @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B_1) @ sk_D_3 @ X0 @ 
% 0.45/0.69             (k1_relat_1 @ sk_D_3))
% 0.45/0.69          | ((sk_C) = (k1_xboole_0))
% 0.45/0.69          | (zip_tseitin_2 @ sk_D_3 @ X0 @ (k1_relat_1 @ sk_D_3))
% 0.45/0.69          | ~ (v1_funct_1 @ sk_D_3)
% 0.45/0.69          | ~ (v1_relat_1 @ sk_D_3))),
% 0.45/0.69      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.69  thf('60', plain, ((v1_funct_1 @ sk_D_3)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('61', plain, ((v1_relat_1 @ sk_D_3)),
% 0.45/0.69      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.69  thf('62', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (zip_tseitin_1 @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B_1) @ sk_D_3 @ X0 @ 
% 0.45/0.69             (k1_relat_1 @ sk_D_3))
% 0.45/0.69          | ((sk_C) = (k1_xboole_0))
% 0.45/0.69          | (zip_tseitin_2 @ sk_D_3 @ X0 @ (k1_relat_1 @ sk_D_3)))),
% 0.45/0.69      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.45/0.69  thf('63', plain,
% 0.45/0.69      (((zip_tseitin_2 @ sk_D_3 @ sk_A @ (k1_relat_1 @ sk_D_3))
% 0.45/0.69        | ((sk_C) = (k1_xboole_0))
% 0.45/0.69        | (zip_tseitin_2 @ sk_D_3 @ sk_A @ (k1_relat_1 @ sk_D_3))
% 0.45/0.69        | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['56', '62'])).
% 0.45/0.69  thf('64', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0))
% 0.45/0.69        | (zip_tseitin_2 @ sk_D_3 @ sk_A @ (k1_relat_1 @ sk_D_3)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['63'])).
% 0.45/0.69  thf('65', plain,
% 0.45/0.69      (((zip_tseitin_2 @ sk_D_3 @ sk_A @ sk_B_1)
% 0.45/0.69        | ((sk_C) = (k1_xboole_0))
% 0.45/0.69        | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['24', '64'])).
% 0.45/0.69  thf('66', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_D_3 @ sk_A @ sk_B_1))),
% 0.45/0.69      inference('simplify', [status(thm)], ['65'])).
% 0.45/0.69  thf('67', plain,
% 0.45/0.69      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.45/0.69         ((v1_funct_2 @ X42 @ X44 @ X43) | ~ (zip_tseitin_2 @ X42 @ X43 @ X44))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.45/0.69  thf('68', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0)) | (v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['66', '67'])).
% 0.45/0.69  thf('69', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_D_3 @ sk_A @ sk_B_1))),
% 0.45/0.69      inference('simplify', [status(thm)], ['65'])).
% 0.45/0.69  thf('70', plain,
% 0.45/0.69      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.45/0.69         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.45/0.69          | ~ (zip_tseitin_2 @ X42 @ X43 @ X44))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.45/0.69  thf('71', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0))
% 0.45/0.69        | (m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.69  thf('72', plain,
% 0.45/0.69      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.69         (((X33) = (k1_xboole_0))
% 0.45/0.69          | ~ (v1_funct_1 @ X32)
% 0.45/0.69          | ~ (v1_funct_2 @ X32 @ X31 @ X33)
% 0.45/0.69          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X33)))
% 0.45/0.69          | (r2_hidden @ X32 @ (k1_funct_2 @ X31 @ X33)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t11_funct_2])).
% 0.45/0.69  thf('73', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0))
% 0.45/0.69        | (r2_hidden @ sk_D_3 @ (k1_funct_2 @ sk_B_1 @ sk_A))
% 0.45/0.69        | ~ (v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_A)
% 0.45/0.69        | ~ (v1_funct_1 @ sk_D_3)
% 0.45/0.69        | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.69  thf('74', plain, ((v1_funct_1 @ sk_D_3)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('75', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0))
% 0.45/0.69        | (r2_hidden @ sk_D_3 @ (k1_funct_2 @ sk_B_1 @ sk_A))
% 0.45/0.69        | ~ (v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_A)
% 0.45/0.69        | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['73', '74'])).
% 0.45/0.69  thf('76', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0))
% 0.45/0.69        | ((sk_A) = (k1_xboole_0))
% 0.45/0.69        | (r2_hidden @ sk_D_3 @ (k1_funct_2 @ sk_B_1 @ sk_A))
% 0.45/0.69        | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['68', '75'])).
% 0.45/0.69  thf('77', plain,
% 0.45/0.69      (((r2_hidden @ sk_D_3 @ (k1_funct_2 @ sk_B_1 @ sk_A))
% 0.45/0.69        | ((sk_A) = (k1_xboole_0))
% 0.45/0.69        | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['76'])).
% 0.45/0.69  thf('78', plain,
% 0.45/0.69      (![X21 : $i, X22 : $i, X24 : $i]:
% 0.45/0.69         ((zip_tseitin_0 @ (sk_E_1 @ X24 @ X21 @ X22) @ X24 @ X21 @ X22)
% 0.45/0.69          | ~ (r2_hidden @ X24 @ (k1_funct_2 @ X22 @ X21)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['15'])).
% 0.45/0.69  thf('79', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0))
% 0.45/0.69        | ((sk_A) = (k1_xboole_0))
% 0.45/0.69        | (zip_tseitin_0 @ (sk_E_1 @ sk_D_3 @ sk_A @ sk_B_1) @ sk_D_3 @ sk_A @ 
% 0.45/0.69           sk_B_1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['77', '78'])).
% 0.45/0.69  thf('80', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.69         (((X16) = (X14)) | ~ (zip_tseitin_0 @ X14 @ X16 @ X15 @ X17))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.69  thf('81', plain,
% 0.45/0.69      ((((sk_A) = (k1_xboole_0))
% 0.45/0.69        | ((sk_C) = (k1_xboole_0))
% 0.45/0.69        | ((sk_D_3) = (sk_E_1 @ sk_D_3 @ sk_A @ sk_B_1)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['79', '80'])).
% 0.45/0.69  thf('82', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0))
% 0.45/0.69        | ((sk_A) = (k1_xboole_0))
% 0.45/0.69        | (zip_tseitin_0 @ (sk_E_1 @ sk_D_3 @ sk_A @ sk_B_1) @ sk_D_3 @ sk_A @ 
% 0.45/0.69           sk_B_1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['77', '78'])).
% 0.45/0.69  thf('83', plain,
% 0.45/0.69      (((zip_tseitin_0 @ sk_D_3 @ sk_D_3 @ sk_A @ sk_B_1)
% 0.45/0.69        | ((sk_C) = (k1_xboole_0))
% 0.45/0.69        | ((sk_A) = (k1_xboole_0))
% 0.45/0.69        | ((sk_A) = (k1_xboole_0))
% 0.45/0.69        | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['81', '82'])).
% 0.45/0.69  thf('84', plain,
% 0.45/0.69      ((((sk_A) = (k1_xboole_0))
% 0.45/0.69        | ((sk_C) = (k1_xboole_0))
% 0.45/0.69        | (zip_tseitin_0 @ sk_D_3 @ sk_D_3 @ sk_A @ sk_B_1))),
% 0.45/0.69      inference('simplify', [status(thm)], ['83'])).
% 0.45/0.69  thf('85', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.69         ((r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.45/0.69          | ~ (zip_tseitin_0 @ X14 @ X16 @ X15 @ X17))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.69  thf('86', plain,
% 0.45/0.69      ((((sk_C) = (k1_xboole_0))
% 0.45/0.69        | ((sk_A) = (k1_xboole_0))
% 0.45/0.69        | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['84', '85'])).
% 0.45/0.69  thf('87', plain,
% 0.45/0.69      (~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_3) @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('88', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.69  thf('89', plain,
% 0.45/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.69         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.45/0.69          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.69  thf('90', plain,
% 0.45/0.69      (((k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 0.45/0.69      inference('sup-', [status(thm)], ['88', '89'])).
% 0.45/0.69  thf('91', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_3) @ sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['87', '90'])).
% 0.45/0.69  thf('92', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.69      inference('clc', [status(thm)], ['86', '91'])).
% 0.45/0.69  thf('93', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('94', plain,
% 0.45/0.69      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['92', '93'])).
% 0.45/0.69  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.69  thf('95', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.69  thf('96', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.69      inference('demod', [status(thm)], ['94', '95'])).
% 0.45/0.69  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.69  thf('98', plain, ($false),
% 0.45/0.69      inference('demod', [status(thm)], ['8', '96', '97'])).
% 0.45/0.69  
% 0.45/0.69  % SZS output end Refutation
% 0.45/0.69  
% 0.45/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
