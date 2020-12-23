%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nQkJDcPzrT

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:33 EST 2020

% Result     : Theorem 20.46s
% Output     : Refutation 20.46s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 136 expanded)
%              Number of leaves         :   39 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  866 (2268 expanded)
%              Number of equality atoms :   53 (  88 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
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

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('16',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( X8 = X11 )
      | ~ ( r2_relset_1 @ X9 @ X10 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('36',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('37',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('38',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('41',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X32 @ X30 @ X30 @ X31 @ X33 @ X29 ) )
      | ( v2_funct_1 @ X33 )
      | ( X31 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X30 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('47',plain,(
    ! [X1: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47','48','49','50'])).

thf('52',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','53'])).

thf('55',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('56',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('57',plain,(
    ! [X1: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('58',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nQkJDcPzrT
% 0.15/0.37  % Computer   : n006.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 09:54:38 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 20.46/20.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 20.46/20.67  % Solved by: fo/fo7.sh
% 20.46/20.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.46/20.67  % done 12029 iterations in 20.209s
% 20.46/20.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 20.46/20.67  % SZS output start Refutation
% 20.46/20.67  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 20.46/20.67  thf(sk_B_type, type, sk_B: $i).
% 20.46/20.67  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 20.46/20.67  thf(sk_C_type, type, sk_C: $i).
% 20.46/20.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 20.46/20.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 20.46/20.67  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 20.46/20.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 20.46/20.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 20.46/20.67  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 20.46/20.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 20.46/20.67  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 20.46/20.67  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 20.46/20.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 20.46/20.67  thf(sk_A_type, type, sk_A: $i).
% 20.46/20.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 20.46/20.67  thf(sk_D_type, type, sk_D: $i).
% 20.46/20.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 20.46/20.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 20.46/20.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 20.46/20.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 20.46/20.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 20.46/20.67  thf(t37_funct_2, conjecture,
% 20.46/20.67    (![A:$i,B:$i,C:$i]:
% 20.46/20.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 20.46/20.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 20.46/20.67       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 20.46/20.67            ( ?[D:$i]:
% 20.46/20.67              ( ( r2_relset_1 @
% 20.46/20.67                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 20.46/20.67                  ( k6_partfun1 @ A ) ) & 
% 20.46/20.67                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 20.46/20.67                ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 20.46/20.67            ( ~( v2_funct_1 @ C ) ) ) ) ))).
% 20.46/20.67  thf(zf_stmt_0, negated_conjecture,
% 20.46/20.67    (~( ![A:$i,B:$i,C:$i]:
% 20.46/20.67        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 20.46/20.67            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 20.46/20.67          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 20.46/20.67               ( ?[D:$i]:
% 20.46/20.67                 ( ( r2_relset_1 @
% 20.46/20.67                     A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 20.46/20.67                     ( k6_partfun1 @ A ) ) & 
% 20.46/20.67                   ( m1_subset_1 @
% 20.46/20.67                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 20.46/20.67                   ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 20.46/20.67               ( ~( v2_funct_1 @ C ) ) ) ) ) )),
% 20.46/20.67    inference('cnf.neg', [status(esa)], [t37_funct_2])).
% 20.46/20.67  thf('0', plain, (~ (v2_funct_1 @ sk_C)),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf('1', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf(d1_funct_2, axiom,
% 20.46/20.67    (![A:$i,B:$i,C:$i]:
% 20.46/20.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.46/20.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 20.46/20.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 20.46/20.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 20.46/20.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 20.46/20.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 20.46/20.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 20.46/20.67  thf(zf_stmt_1, axiom,
% 20.46/20.67    (![C:$i,B:$i,A:$i]:
% 20.46/20.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 20.46/20.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 20.46/20.67  thf('2', plain,
% 20.46/20.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 20.46/20.67         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 20.46/20.67          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 20.46/20.67          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 20.46/20.67  thf('3', plain,
% 20.46/20.67      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 20.46/20.67        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 20.46/20.67      inference('sup-', [status(thm)], ['1', '2'])).
% 20.46/20.67  thf(zf_stmt_2, axiom,
% 20.46/20.67    (![B:$i,A:$i]:
% 20.46/20.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 20.46/20.67       ( zip_tseitin_0 @ B @ A ) ))).
% 20.46/20.67  thf('4', plain,
% 20.46/20.67      (![X12 : $i, X13 : $i]:
% 20.46/20.67         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 20.46/20.67  thf('5', plain,
% 20.46/20.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 20.46/20.67  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 20.46/20.67  thf(zf_stmt_5, axiom,
% 20.46/20.67    (![A:$i,B:$i,C:$i]:
% 20.46/20.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.46/20.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 20.46/20.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 20.46/20.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 20.46/20.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 20.46/20.67  thf('6', plain,
% 20.46/20.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 20.46/20.67         (~ (zip_tseitin_0 @ X17 @ X18)
% 20.46/20.67          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 20.46/20.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 20.46/20.67  thf('7', plain,
% 20.46/20.67      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 20.46/20.67      inference('sup-', [status(thm)], ['5', '6'])).
% 20.46/20.67  thf('8', plain,
% 20.46/20.67      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 20.46/20.67      inference('sup-', [status(thm)], ['4', '7'])).
% 20.46/20.67  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf('10', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 20.46/20.67      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 20.46/20.67  thf('11', plain,
% 20.46/20.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf(redefinition_k1_relset_1, axiom,
% 20.46/20.67    (![A:$i,B:$i,C:$i]:
% 20.46/20.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.46/20.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 20.46/20.67  thf('12', plain,
% 20.46/20.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 20.46/20.67         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 20.46/20.67          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 20.46/20.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 20.46/20.67  thf('13', plain,
% 20.46/20.67      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 20.46/20.67      inference('sup-', [status(thm)], ['11', '12'])).
% 20.46/20.67  thf('14', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 20.46/20.67      inference('demod', [status(thm)], ['3', '10', '13'])).
% 20.46/20.67  thf(t64_relat_1, axiom,
% 20.46/20.67    (![A:$i]:
% 20.46/20.67     ( ( v1_relat_1 @ A ) =>
% 20.46/20.67       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 20.46/20.67           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 20.46/20.67         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 20.46/20.67  thf('15', plain,
% 20.46/20.67      (![X0 : $i]:
% 20.46/20.67         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 20.46/20.67          | ((X0) = (k1_xboole_0))
% 20.46/20.67          | ~ (v1_relat_1 @ X0))),
% 20.46/20.67      inference('cnf', [status(esa)], [t64_relat_1])).
% 20.46/20.67  thf('16', plain,
% 20.46/20.67      ((((sk_A) != (k1_xboole_0))
% 20.46/20.67        | ~ (v1_relat_1 @ sk_C)
% 20.46/20.67        | ((sk_C) = (k1_xboole_0)))),
% 20.46/20.67      inference('sup-', [status(thm)], ['14', '15'])).
% 20.46/20.67  thf('17', plain,
% 20.46/20.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf(cc1_relset_1, axiom,
% 20.46/20.67    (![A:$i,B:$i,C:$i]:
% 20.46/20.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.46/20.67       ( v1_relat_1 @ C ) ))).
% 20.46/20.67  thf('18', plain,
% 20.46/20.67      (![X2 : $i, X3 : $i, X4 : $i]:
% 20.46/20.67         ((v1_relat_1 @ X2)
% 20.46/20.67          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 20.46/20.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 20.46/20.67  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 20.46/20.67      inference('sup-', [status(thm)], ['17', '18'])).
% 20.46/20.67  thf('20', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 20.46/20.67      inference('demod', [status(thm)], ['16', '19'])).
% 20.46/20.67  thf('21', plain,
% 20.46/20.67      ((r2_relset_1 @ sk_A @ sk_A @ 
% 20.46/20.67        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 20.46/20.67        (k6_partfun1 @ sk_A))),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf(redefinition_k6_partfun1, axiom,
% 20.46/20.67    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 20.46/20.67  thf('22', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 20.46/20.67      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 20.46/20.67  thf('23', plain,
% 20.46/20.67      ((r2_relset_1 @ sk_A @ sk_A @ 
% 20.46/20.67        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 20.46/20.67        (k6_relat_1 @ sk_A))),
% 20.46/20.67      inference('demod', [status(thm)], ['21', '22'])).
% 20.46/20.67  thf('24', plain,
% 20.46/20.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf('25', plain,
% 20.46/20.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf(dt_k1_partfun1, axiom,
% 20.46/20.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 20.46/20.67     ( ( ( v1_funct_1 @ E ) & 
% 20.46/20.67         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 20.46/20.67         ( v1_funct_1 @ F ) & 
% 20.46/20.67         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 20.46/20.67       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 20.46/20.67         ( m1_subset_1 @
% 20.46/20.67           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 20.46/20.67           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 20.46/20.67  thf('26', plain,
% 20.46/20.67      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 20.46/20.67         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 20.46/20.67          | ~ (v1_funct_1 @ X20)
% 20.46/20.67          | ~ (v1_funct_1 @ X23)
% 20.46/20.67          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 20.46/20.67          | (m1_subset_1 @ (k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23) @ 
% 20.46/20.67             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X25))))),
% 20.46/20.67      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 20.46/20.67  thf('27', plain,
% 20.46/20.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.46/20.67         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 20.46/20.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 20.46/20.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 20.46/20.67          | ~ (v1_funct_1 @ X1)
% 20.46/20.67          | ~ (v1_funct_1 @ sk_C))),
% 20.46/20.67      inference('sup-', [status(thm)], ['25', '26'])).
% 20.46/20.67  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf('29', plain,
% 20.46/20.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.46/20.67         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 20.46/20.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 20.46/20.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 20.46/20.67          | ~ (v1_funct_1 @ X1))),
% 20.46/20.67      inference('demod', [status(thm)], ['27', '28'])).
% 20.46/20.67  thf('30', plain,
% 20.46/20.67      ((~ (v1_funct_1 @ sk_D)
% 20.46/20.67        | (m1_subset_1 @ 
% 20.46/20.67           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 20.46/20.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 20.46/20.67      inference('sup-', [status(thm)], ['24', '29'])).
% 20.46/20.67  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf('32', plain,
% 20.46/20.67      ((m1_subset_1 @ 
% 20.46/20.67        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 20.46/20.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 20.46/20.67      inference('demod', [status(thm)], ['30', '31'])).
% 20.46/20.67  thf(redefinition_r2_relset_1, axiom,
% 20.46/20.67    (![A:$i,B:$i,C:$i,D:$i]:
% 20.46/20.67     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 20.46/20.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 20.46/20.67       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 20.46/20.67  thf('33', plain,
% 20.46/20.67      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 20.46/20.67         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 20.46/20.67          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 20.46/20.67          | ((X8) = (X11))
% 20.46/20.67          | ~ (r2_relset_1 @ X9 @ X10 @ X8 @ X11))),
% 20.46/20.67      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 20.46/20.67  thf('34', plain,
% 20.46/20.67      (![X0 : $i]:
% 20.46/20.67         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 20.46/20.67             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 20.46/20.67          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 20.46/20.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 20.46/20.67      inference('sup-', [status(thm)], ['32', '33'])).
% 20.46/20.67  thf('35', plain,
% 20.46/20.67      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 20.46/20.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 20.46/20.67        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 20.46/20.67            = (k6_relat_1 @ sk_A)))),
% 20.46/20.67      inference('sup-', [status(thm)], ['23', '34'])).
% 20.46/20.67  thf(dt_k6_partfun1, axiom,
% 20.46/20.67    (![A:$i]:
% 20.46/20.67     ( ( m1_subset_1 @
% 20.46/20.67         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 20.46/20.67       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 20.46/20.67  thf('36', plain,
% 20.46/20.67      (![X27 : $i]:
% 20.46/20.67         (m1_subset_1 @ (k6_partfun1 @ X27) @ 
% 20.46/20.67          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 20.46/20.67      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 20.46/20.67  thf('37', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 20.46/20.67      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 20.46/20.67  thf('38', plain,
% 20.46/20.67      (![X27 : $i]:
% 20.46/20.67         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 20.46/20.67          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 20.46/20.67      inference('demod', [status(thm)], ['36', '37'])).
% 20.46/20.67  thf('39', plain,
% 20.46/20.67      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 20.46/20.67         = (k6_relat_1 @ sk_A))),
% 20.46/20.67      inference('demod', [status(thm)], ['35', '38'])).
% 20.46/20.67  thf('40', plain,
% 20.46/20.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf(t26_funct_2, axiom,
% 20.46/20.67    (![A:$i,B:$i,C:$i,D:$i]:
% 20.46/20.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 20.46/20.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 20.46/20.67       ( ![E:$i]:
% 20.46/20.67         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 20.46/20.67             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 20.46/20.67           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 20.46/20.67             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 20.46/20.67               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 20.46/20.67  thf('41', plain,
% 20.46/20.67      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 20.46/20.67         (~ (v1_funct_1 @ X29)
% 20.46/20.67          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 20.46/20.67          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 20.46/20.67          | ~ (v2_funct_1 @ (k1_partfun1 @ X32 @ X30 @ X30 @ X31 @ X33 @ X29))
% 20.46/20.67          | (v2_funct_1 @ X33)
% 20.46/20.67          | ((X31) = (k1_xboole_0))
% 20.46/20.67          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X30)))
% 20.46/20.67          | ~ (v1_funct_2 @ X33 @ X32 @ X30)
% 20.46/20.67          | ~ (v1_funct_1 @ X33))),
% 20.46/20.67      inference('cnf', [status(esa)], [t26_funct_2])).
% 20.46/20.67  thf('42', plain,
% 20.46/20.67      (![X0 : $i, X1 : $i]:
% 20.46/20.67         (~ (v1_funct_1 @ X0)
% 20.46/20.67          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 20.46/20.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 20.46/20.67          | ((sk_A) = (k1_xboole_0))
% 20.46/20.67          | (v2_funct_1 @ X0)
% 20.46/20.67          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 20.46/20.67          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 20.46/20.67          | ~ (v1_funct_1 @ sk_D))),
% 20.46/20.67      inference('sup-', [status(thm)], ['40', '41'])).
% 20.46/20.67  thf('43', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf('45', plain,
% 20.46/20.67      (![X0 : $i, X1 : $i]:
% 20.46/20.67         (~ (v1_funct_1 @ X0)
% 20.46/20.67          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 20.46/20.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 20.46/20.67          | ((sk_A) = (k1_xboole_0))
% 20.46/20.67          | (v2_funct_1 @ X0)
% 20.46/20.67          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 20.46/20.67      inference('demod', [status(thm)], ['42', '43', '44'])).
% 20.46/20.67  thf('46', plain,
% 20.46/20.67      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 20.46/20.67        | (v2_funct_1 @ sk_C)
% 20.46/20.67        | ((sk_A) = (k1_xboole_0))
% 20.46/20.67        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 20.46/20.67        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 20.46/20.67        | ~ (v1_funct_1 @ sk_C))),
% 20.46/20.67      inference('sup-', [status(thm)], ['39', '45'])).
% 20.46/20.67  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 20.46/20.67  thf('47', plain, (![X1 : $i]: (v2_funct_1 @ (k6_relat_1 @ X1))),
% 20.46/20.67      inference('cnf', [status(esa)], [t52_funct_1])).
% 20.46/20.67  thf('48', plain,
% 20.46/20.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf('49', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf('51', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 20.46/20.67      inference('demod', [status(thm)], ['46', '47', '48', '49', '50'])).
% 20.46/20.67  thf('52', plain, (~ (v2_funct_1 @ sk_C)),
% 20.46/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.46/20.67  thf('53', plain, (((sk_A) = (k1_xboole_0))),
% 20.46/20.67      inference('clc', [status(thm)], ['51', '52'])).
% 20.46/20.67  thf('54', plain,
% 20.46/20.67      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 20.46/20.67      inference('demod', [status(thm)], ['20', '53'])).
% 20.46/20.67  thf('55', plain, (((sk_C) = (k1_xboole_0))),
% 20.46/20.67      inference('simplify', [status(thm)], ['54'])).
% 20.46/20.67  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 20.46/20.67  thf('56', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 20.46/20.67      inference('cnf', [status(esa)], [t81_relat_1])).
% 20.46/20.67  thf('57', plain, (![X1 : $i]: (v2_funct_1 @ (k6_relat_1 @ X1))),
% 20.46/20.67      inference('cnf', [status(esa)], [t52_funct_1])).
% 20.46/20.67  thf('58', plain, ((v2_funct_1 @ k1_xboole_0)),
% 20.46/20.67      inference('sup+', [status(thm)], ['56', '57'])).
% 20.46/20.67  thf('59', plain, ($false),
% 20.46/20.67      inference('demod', [status(thm)], ['0', '55', '58'])).
% 20.46/20.67  
% 20.46/20.67  % SZS output end Refutation
% 20.46/20.67  
% 20.46/20.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
