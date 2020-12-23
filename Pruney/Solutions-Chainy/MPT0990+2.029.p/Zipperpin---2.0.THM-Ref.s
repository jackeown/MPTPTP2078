%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JJxB12esqD

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:59 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 250 expanded)
%              Number of leaves         :   43 (  93 expanded)
%              Depth                    :   17
%              Number of atoms          : 1486 (5869 expanded)
%              Number of equality atoms :  119 ( 437 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 )
        = ( k5_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('26',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
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

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('35',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('36',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['32','39','42'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('47',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X39 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X40 ) @ X40 )
        = ( k6_partfun1 @ X39 ) )
      | ~ ( v2_funct_1 @ X40 )
      | ( ( k2_relset_1 @ X41 @ X39 @ X40 )
       != X39 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('48',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('49',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X39 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X40 ) @ X40 )
        = ( k6_relat_1 @ X39 ) )
      | ~ ( v2_funct_1 @ X40 )
      | ( ( k2_relset_1 @ X41 @ X39 @ X40 )
       != X39 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(l72_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ! [D: $i] :
              ( ( ( v1_relat_1 @ D )
                & ( v1_funct_1 @ D ) )
             => ( ( ( ( k2_relat_1 @ B )
                    = A )
                  & ( ( k5_relat_1 @ B @ C )
                    = ( k6_relat_1 @ ( k1_relat_1 @ D ) ) )
                  & ( ( k5_relat_1 @ C @ D )
                    = ( k6_relat_1 @ A ) ) )
               => ( D = B ) ) ) ) ) )).

thf('60',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X3 )
       != X2 )
      | ( ( k5_relat_1 @ X3 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ( ( k5_relat_1 @ X1 @ X4 )
       != ( k6_relat_1 @ X2 ) )
      | ( X4 = X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l72_funct_1])).

thf('61',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4 = X3 )
      | ( ( k5_relat_1 @ X1 @ X4 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
      | ( ( k5_relat_1 @ X3 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ X2 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X2 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ sk_B )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['58','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('66',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('71',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('73',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('77',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('83',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['73','80','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ sk_B )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['63','64','67','68','69','70','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_relat_1 @ sk_A ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k6_relat_1 @ sk_B )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_relat_1 @ sk_A ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k6_relat_1 @ sk_B )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k6_relat_1 @ sk_B )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ sk_B )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_relat_1 @ sk_A ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['43','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('98',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_relat_1 @ sk_A ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['94','95','98'])).

thf('100',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ( k5_relat_1 @ sk_C @ sk_D )
 != ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

thf('103',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JJxB12esqD
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:37:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.71/0.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.71/0.92  % Solved by: fo/fo7.sh
% 0.71/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.92  % done 268 iterations in 0.488s
% 0.71/0.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.71/0.92  % SZS output start Refutation
% 0.71/0.92  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.71/0.92  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.71/0.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.71/0.92  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.71/0.92  thf(sk_C_type, type, sk_C: $i).
% 0.71/0.92  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.71/0.92  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.71/0.92  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.71/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.71/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.92  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.71/0.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.71/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.71/0.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.71/0.92  thf(sk_D_type, type, sk_D: $i).
% 0.71/0.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.71/0.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.71/0.92  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.71/0.92  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.71/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.71/0.92  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.71/0.92  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.71/0.92  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.71/0.92  thf(t36_funct_2, conjecture,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.71/0.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.92       ( ![D:$i]:
% 0.71/0.92         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.71/0.92             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.71/0.92           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.71/0.92               ( r2_relset_1 @
% 0.71/0.92                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.71/0.92                 ( k6_partfun1 @ A ) ) & 
% 0.71/0.92               ( v2_funct_1 @ C ) ) =>
% 0.71/0.92             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.71/0.92               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.71/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.92    (~( ![A:$i,B:$i,C:$i]:
% 0.71/0.92        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.71/0.92            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.92          ( ![D:$i]:
% 0.71/0.92            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.71/0.92                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.71/0.92              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.71/0.92                  ( r2_relset_1 @
% 0.71/0.92                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.71/0.92                    ( k6_partfun1 @ A ) ) & 
% 0.71/0.92                  ( v2_funct_1 @ C ) ) =>
% 0.71/0.92                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.71/0.92                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.71/0.92    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.71/0.92  thf('0', plain,
% 0.71/0.92      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.92        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.71/0.92        (k6_partfun1 @ sk_A))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(redefinition_k6_partfun1, axiom,
% 0.71/0.92    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.71/0.92  thf('1', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.71/0.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.71/0.92  thf('2', plain,
% 0.71/0.92      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.92        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.71/0.92        (k6_relat_1 @ sk_A))),
% 0.71/0.92      inference('demod', [status(thm)], ['0', '1'])).
% 0.71/0.92  thf('3', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('4', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(redefinition_k1_partfun1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.71/0.92     ( ( ( v1_funct_1 @ E ) & 
% 0.71/0.92         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.71/0.92         ( v1_funct_1 @ F ) & 
% 0.71/0.92         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.71/0.92       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.71/0.92  thf('5', plain,
% 0.71/0.92      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.71/0.92         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.71/0.92          | ~ (v1_funct_1 @ X32)
% 0.71/0.92          | ~ (v1_funct_1 @ X35)
% 0.71/0.92          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.71/0.92          | ((k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)
% 0.71/0.92              = (k5_relat_1 @ X32 @ X35)))),
% 0.71/0.92      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.71/0.92  thf('6', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.92         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.71/0.92            = (k5_relat_1 @ sk_C @ X0))
% 0.71/0.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.71/0.92          | ~ (v1_funct_1 @ X0)
% 0.71/0.92          | ~ (v1_funct_1 @ sk_C))),
% 0.71/0.92      inference('sup-', [status(thm)], ['4', '5'])).
% 0.71/0.92  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('8', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.92         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.71/0.92            = (k5_relat_1 @ sk_C @ X0))
% 0.71/0.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.71/0.92          | ~ (v1_funct_1 @ X0))),
% 0.71/0.92      inference('demod', [status(thm)], ['6', '7'])).
% 0.71/0.92  thf('9', plain,
% 0.71/0.92      ((~ (v1_funct_1 @ sk_D)
% 0.71/0.92        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.71/0.92            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['3', '8'])).
% 0.71/0.92  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('11', plain,
% 0.71/0.92      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.71/0.92         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.71/0.92      inference('demod', [status(thm)], ['9', '10'])).
% 0.71/0.92  thf('12', plain,
% 0.71/0.92      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.71/0.92        (k6_relat_1 @ sk_A))),
% 0.71/0.92      inference('demod', [status(thm)], ['2', '11'])).
% 0.71/0.92  thf('13', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('14', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(dt_k1_partfun1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.71/0.92     ( ( ( v1_funct_1 @ E ) & 
% 0.71/0.92         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.71/0.92         ( v1_funct_1 @ F ) & 
% 0.71/0.92         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.71/0.92       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.71/0.92         ( m1_subset_1 @
% 0.71/0.92           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.71/0.92           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.71/0.92  thf('15', plain,
% 0.71/0.92      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.71/0.92         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.71/0.92          | ~ (v1_funct_1 @ X24)
% 0.71/0.92          | ~ (v1_funct_1 @ X27)
% 0.71/0.92          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.71/0.92          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 0.71/0.92             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 0.71/0.92      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.71/0.92  thf('16', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.92         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.71/0.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.71/0.92          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.71/0.92          | ~ (v1_funct_1 @ X1)
% 0.71/0.92          | ~ (v1_funct_1 @ sk_C))),
% 0.71/0.92      inference('sup-', [status(thm)], ['14', '15'])).
% 0.71/0.92  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('18', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.92         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.71/0.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.71/0.92          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.71/0.92          | ~ (v1_funct_1 @ X1))),
% 0.71/0.92      inference('demod', [status(thm)], ['16', '17'])).
% 0.71/0.92  thf('19', plain,
% 0.71/0.92      ((~ (v1_funct_1 @ sk_D)
% 0.71/0.92        | (m1_subset_1 @ 
% 0.71/0.92           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.71/0.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.71/0.92      inference('sup-', [status(thm)], ['13', '18'])).
% 0.71/0.92  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('21', plain,
% 0.71/0.92      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.71/0.92         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.71/0.92      inference('demod', [status(thm)], ['9', '10'])).
% 0.71/0.92  thf('22', plain,
% 0.71/0.92      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.71/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.71/0.92      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.71/0.92  thf(redefinition_r2_relset_1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.92     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.71/0.92         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.92       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.71/0.92  thf('23', plain,
% 0.71/0.92      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.71/0.92         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.71/0.92          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.71/0.92          | ((X12) = (X15))
% 0.71/0.92          | ~ (r2_relset_1 @ X13 @ X14 @ X12 @ X15))),
% 0.71/0.92      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.71/0.92  thf('24', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.71/0.92          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.71/0.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.71/0.92      inference('sup-', [status(thm)], ['22', '23'])).
% 0.71/0.92  thf('25', plain,
% 0.71/0.92      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.71/0.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.71/0.92        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['12', '24'])).
% 0.71/0.92  thf(dt_k6_partfun1, axiom,
% 0.71/0.92    (![A:$i]:
% 0.71/0.92     ( ( m1_subset_1 @
% 0.71/0.92         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.71/0.92       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.71/0.92  thf('26', plain,
% 0.71/0.92      (![X31 : $i]:
% 0.71/0.92         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 0.71/0.92          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.71/0.92      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.71/0.92  thf('27', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.71/0.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.71/0.92  thf('28', plain,
% 0.71/0.92      (![X31 : $i]:
% 0.71/0.92         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 0.71/0.92          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.71/0.92      inference('demod', [status(thm)], ['26', '27'])).
% 0.71/0.92  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.71/0.92      inference('demod', [status(thm)], ['25', '28'])).
% 0.71/0.92  thf('30', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(d1_funct_2, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.92       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.71/0.92           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.71/0.92             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.71/0.92         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.71/0.92           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.71/0.92             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.71/0.92  thf(zf_stmt_1, axiom,
% 0.71/0.92    (![C:$i,B:$i,A:$i]:
% 0.71/0.92     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.71/0.92       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.71/0.92  thf('31', plain,
% 0.71/0.92      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.71/0.92         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.71/0.92          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.71/0.92          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.71/0.92  thf('32', plain,
% 0.71/0.92      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.71/0.92        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['30', '31'])).
% 0.71/0.92  thf(zf_stmt_2, axiom,
% 0.71/0.92    (![B:$i,A:$i]:
% 0.71/0.92     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.71/0.92       ( zip_tseitin_0 @ B @ A ) ))).
% 0.71/0.92  thf('33', plain,
% 0.71/0.92      (![X16 : $i, X17 : $i]:
% 0.71/0.92         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.71/0.92  thf('34', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.71/0.92  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.71/0.92  thf(zf_stmt_5, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.92       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.71/0.92         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.71/0.92           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.71/0.92             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.71/0.92  thf('35', plain,
% 0.71/0.92      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.71/0.92         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.71/0.92          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.71/0.92          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.71/0.92  thf('36', plain,
% 0.71/0.92      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.71/0.92      inference('sup-', [status(thm)], ['34', '35'])).
% 0.71/0.92  thf('37', plain,
% 0.71/0.92      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.71/0.92      inference('sup-', [status(thm)], ['33', '36'])).
% 0.71/0.92  thf('38', plain, (((sk_A) != (k1_xboole_0))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('39', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.71/0.92      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.71/0.92  thf('40', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(redefinition_k1_relset_1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.92       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.71/0.92  thf('41', plain,
% 0.71/0.92      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.71/0.92         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.71/0.92          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.71/0.92      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.71/0.92  thf('42', plain,
% 0.71/0.92      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.71/0.92      inference('sup-', [status(thm)], ['40', '41'])).
% 0.71/0.92  thf('43', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.71/0.92      inference('demod', [status(thm)], ['32', '39', '42'])).
% 0.71/0.92  thf(dt_k2_funct_1, axiom,
% 0.71/0.92    (![A:$i]:
% 0.71/0.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.71/0.92       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.71/0.92         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.71/0.92  thf('44', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.71/0.92          | ~ (v1_funct_1 @ X0)
% 0.71/0.92          | ~ (v1_relat_1 @ X0))),
% 0.71/0.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.71/0.92  thf('45', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.71/0.92          | ~ (v1_funct_1 @ X0)
% 0.71/0.92          | ~ (v1_relat_1 @ X0))),
% 0.71/0.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.71/0.92  thf('46', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(t35_funct_2, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.71/0.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.92       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.71/0.92         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.71/0.92           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.71/0.92             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.71/0.92  thf('47', plain,
% 0.71/0.92      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.71/0.92         (((X39) = (k1_xboole_0))
% 0.71/0.92          | ~ (v1_funct_1 @ X40)
% 0.71/0.92          | ~ (v1_funct_2 @ X40 @ X41 @ X39)
% 0.71/0.92          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X39)))
% 0.71/0.92          | ((k5_relat_1 @ (k2_funct_1 @ X40) @ X40) = (k6_partfun1 @ X39))
% 0.71/0.92          | ~ (v2_funct_1 @ X40)
% 0.71/0.92          | ((k2_relset_1 @ X41 @ X39 @ X40) != (X39)))),
% 0.71/0.92      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.71/0.92  thf('48', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.71/0.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.71/0.92  thf('49', plain,
% 0.71/0.92      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.71/0.92         (((X39) = (k1_xboole_0))
% 0.71/0.92          | ~ (v1_funct_1 @ X40)
% 0.71/0.92          | ~ (v1_funct_2 @ X40 @ X41 @ X39)
% 0.71/0.92          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X39)))
% 0.71/0.92          | ((k5_relat_1 @ (k2_funct_1 @ X40) @ X40) = (k6_relat_1 @ X39))
% 0.71/0.92          | ~ (v2_funct_1 @ X40)
% 0.71/0.92          | ((k2_relset_1 @ X41 @ X39 @ X40) != (X39)))),
% 0.71/0.92      inference('demod', [status(thm)], ['47', '48'])).
% 0.71/0.92  thf('50', plain,
% 0.71/0.92      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.71/0.92        | ~ (v2_funct_1 @ sk_C)
% 0.71/0.92        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 0.71/0.92        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.71/0.92        | ~ (v1_funct_1 @ sk_C)
% 0.71/0.92        | ((sk_B) = (k1_xboole_0)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['46', '49'])).
% 0.71/0.92  thf('51', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('52', plain, ((v2_funct_1 @ sk_C)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('53', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('55', plain,
% 0.71/0.92      ((((sk_B) != (sk_B))
% 0.71/0.92        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 0.71/0.92        | ((sk_B) = (k1_xboole_0)))),
% 0.71/0.92      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.71/0.92  thf('56', plain,
% 0.71/0.92      ((((sk_B) = (k1_xboole_0))
% 0.71/0.92        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 0.71/0.92      inference('simplify', [status(thm)], ['55'])).
% 0.71/0.92  thf('57', plain, (((sk_B) != (k1_xboole_0))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('58', plain,
% 0.71/0.92      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.71/0.92      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.71/0.92  thf(t55_funct_1, axiom,
% 0.71/0.92    (![A:$i]:
% 0.71/0.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.71/0.92       ( ( v2_funct_1 @ A ) =>
% 0.71/0.92         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.71/0.92           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.71/0.92  thf('59', plain,
% 0.71/0.92      (![X5 : $i]:
% 0.71/0.92         (~ (v2_funct_1 @ X5)
% 0.71/0.92          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.71/0.92          | ~ (v1_funct_1 @ X5)
% 0.71/0.92          | ~ (v1_relat_1 @ X5))),
% 0.71/0.92      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.71/0.92  thf(l72_funct_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.71/0.92       ( ![C:$i]:
% 0.71/0.92         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.71/0.92           ( ![D:$i]:
% 0.71/0.92             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.71/0.92               ( ( ( ( k2_relat_1 @ B ) = ( A ) ) & 
% 0.71/0.92                   ( ( k5_relat_1 @ B @ C ) =
% 0.71/0.92                     ( k6_relat_1 @ ( k1_relat_1 @ D ) ) ) & 
% 0.71/0.92                   ( ( k5_relat_1 @ C @ D ) = ( k6_relat_1 @ A ) ) ) =>
% 0.71/0.92                 ( ( D ) = ( B ) ) ) ) ) ) ) ))).
% 0.71/0.92  thf('60', plain,
% 0.71/0.92      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.71/0.92         (~ (v1_relat_1 @ X1)
% 0.71/0.92          | ~ (v1_funct_1 @ X1)
% 0.71/0.92          | ((k2_relat_1 @ X3) != (X2))
% 0.71/0.92          | ((k5_relat_1 @ X3 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.71/0.92          | ((k5_relat_1 @ X1 @ X4) != (k6_relat_1 @ X2))
% 0.71/0.92          | ((X4) = (X3))
% 0.71/0.92          | ~ (v1_funct_1 @ X4)
% 0.71/0.92          | ~ (v1_relat_1 @ X4)
% 0.71/0.92          | ~ (v1_funct_1 @ X3)
% 0.71/0.92          | ~ (v1_relat_1 @ X3))),
% 0.71/0.92      inference('cnf', [status(esa)], [l72_funct_1])).
% 0.71/0.92  thf('61', plain,
% 0.71/0.92      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.71/0.92         (~ (v1_relat_1 @ X3)
% 0.71/0.92          | ~ (v1_funct_1 @ X3)
% 0.71/0.92          | ~ (v1_relat_1 @ X4)
% 0.71/0.92          | ~ (v1_funct_1 @ X4)
% 0.71/0.92          | ((X4) = (X3))
% 0.71/0.92          | ((k5_relat_1 @ X1 @ X4) != (k6_relat_1 @ (k2_relat_1 @ X3)))
% 0.71/0.92          | ((k5_relat_1 @ X3 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.71/0.92          | ~ (v1_funct_1 @ X1)
% 0.71/0.92          | ~ (v1_relat_1 @ X1))),
% 0.71/0.92      inference('simplify', [status(thm)], ['60'])).
% 0.71/0.92  thf('62', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.92         (((k5_relat_1 @ X2 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.71/0.92          | ~ (v1_relat_1 @ X0)
% 0.71/0.92          | ~ (v1_funct_1 @ X0)
% 0.71/0.92          | ~ (v2_funct_1 @ X0)
% 0.71/0.92          | ~ (v1_relat_1 @ X2)
% 0.71/0.92          | ~ (v1_funct_1 @ X2)
% 0.71/0.92          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X2)
% 0.71/0.92              != (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.71/0.92          | ((X1) = (k2_funct_1 @ X0))
% 0.71/0.92          | ~ (v1_funct_1 @ X1)
% 0.71/0.92          | ~ (v1_relat_1 @ X1)
% 0.71/0.92          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.71/0.92          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['59', '61'])).
% 0.71/0.92  thf('63', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         (((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.71/0.92          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.71/0.92          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.71/0.92          | ~ (v1_relat_1 @ X0)
% 0.71/0.92          | ~ (v1_funct_1 @ X0)
% 0.71/0.92          | ((X0) = (k2_funct_1 @ sk_C))
% 0.71/0.92          | ~ (v1_funct_1 @ sk_C)
% 0.71/0.92          | ~ (v1_relat_1 @ sk_C)
% 0.71/0.92          | ~ (v2_funct_1 @ sk_C)
% 0.71/0.92          | ~ (v1_funct_1 @ sk_C)
% 0.71/0.92          | ~ (v1_relat_1 @ sk_C)
% 0.71/0.92          | ((k5_relat_1 @ sk_C @ X0) != (k6_relat_1 @ (k1_relat_1 @ sk_C))))),
% 0.71/0.92      inference('sup-', [status(thm)], ['58', '62'])).
% 0.71/0.92  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('65', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(cc1_relset_1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.92       ( v1_relat_1 @ C ) ))).
% 0.71/0.92  thf('66', plain,
% 0.71/0.92      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.71/0.92         ((v1_relat_1 @ X6)
% 0.71/0.92          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.71/0.92      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.71/0.92  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.71/0.92      inference('sup-', [status(thm)], ['65', '66'])).
% 0.71/0.92  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.71/0.92      inference('sup-', [status(thm)], ['65', '66'])).
% 0.71/0.92  thf('71', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('72', plain,
% 0.71/0.92      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.71/0.92         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.71/0.92          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.71/0.92          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.71/0.92  thf('73', plain,
% 0.71/0.92      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.71/0.92        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['71', '72'])).
% 0.71/0.92  thf('74', plain,
% 0.71/0.92      (![X16 : $i, X17 : $i]:
% 0.71/0.92         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.71/0.92  thf('75', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('76', plain,
% 0.71/0.92      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.71/0.92         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.71/0.92          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.71/0.92          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.71/0.92  thf('77', plain,
% 0.71/0.92      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.71/0.92      inference('sup-', [status(thm)], ['75', '76'])).
% 0.71/0.92  thf('78', plain,
% 0.71/0.92      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.71/0.92      inference('sup-', [status(thm)], ['74', '77'])).
% 0.71/0.92  thf('79', plain, (((sk_B) != (k1_xboole_0))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('80', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.71/0.92      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 0.71/0.92  thf('81', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('82', plain,
% 0.71/0.92      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.71/0.92         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.71/0.92          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.71/0.92      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.71/0.92  thf('83', plain,
% 0.71/0.92      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.71/0.92      inference('sup-', [status(thm)], ['81', '82'])).
% 0.71/0.92  thf('84', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.71/0.92      inference('demod', [status(thm)], ['73', '80', '83'])).
% 0.71/0.92  thf('85', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         (((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.71/0.92          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.71/0.92          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.71/0.92          | ~ (v1_relat_1 @ X0)
% 0.71/0.92          | ~ (v1_funct_1 @ X0)
% 0.71/0.92          | ((X0) = (k2_funct_1 @ sk_C))
% 0.71/0.92          | ((k5_relat_1 @ sk_C @ X0) != (k6_relat_1 @ sk_A)))),
% 0.71/0.92      inference('demod', [status(thm)],
% 0.71/0.92                ['63', '64', '67', '68', '69', '70', '84'])).
% 0.71/0.92  thf('86', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         (~ (v1_relat_1 @ sk_C)
% 0.71/0.92          | ~ (v1_funct_1 @ sk_C)
% 0.71/0.92          | ((k5_relat_1 @ sk_C @ X0) != (k6_relat_1 @ sk_A))
% 0.71/0.92          | ((X0) = (k2_funct_1 @ sk_C))
% 0.71/0.92          | ~ (v1_funct_1 @ X0)
% 0.71/0.92          | ~ (v1_relat_1 @ X0)
% 0.71/0.92          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.71/0.92          | ((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 0.71/0.92      inference('sup-', [status(thm)], ['45', '85'])).
% 0.71/0.92  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 0.71/0.92      inference('sup-', [status(thm)], ['65', '66'])).
% 0.71/0.92  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('89', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         (((k5_relat_1 @ sk_C @ X0) != (k6_relat_1 @ sk_A))
% 0.71/0.92          | ((X0) = (k2_funct_1 @ sk_C))
% 0.71/0.92          | ~ (v1_funct_1 @ X0)
% 0.71/0.92          | ~ (v1_relat_1 @ X0)
% 0.71/0.92          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.71/0.92          | ((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 0.71/0.92      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.71/0.92  thf('90', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         (~ (v1_relat_1 @ sk_C)
% 0.71/0.92          | ~ (v1_funct_1 @ sk_C)
% 0.71/0.92          | ((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.71/0.92          | ~ (v1_relat_1 @ X0)
% 0.71/0.92          | ~ (v1_funct_1 @ X0)
% 0.71/0.92          | ((X0) = (k2_funct_1 @ sk_C))
% 0.71/0.92          | ((k5_relat_1 @ sk_C @ X0) != (k6_relat_1 @ sk_A)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['44', '89'])).
% 0.71/0.92  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 0.71/0.92      inference('sup-', [status(thm)], ['65', '66'])).
% 0.71/0.92  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('93', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         (((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.71/0.92          | ~ (v1_relat_1 @ X0)
% 0.71/0.92          | ~ (v1_funct_1 @ X0)
% 0.71/0.92          | ((X0) = (k2_funct_1 @ sk_C))
% 0.71/0.92          | ((k5_relat_1 @ sk_C @ X0) != (k6_relat_1 @ sk_A)))),
% 0.71/0.92      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.71/0.92  thf('94', plain,
% 0.71/0.92      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 0.71/0.92        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A))
% 0.71/0.92        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.71/0.92        | ~ (v1_funct_1 @ sk_D)
% 0.71/0.92        | ~ (v1_relat_1 @ sk_D))),
% 0.71/0.92      inference('sup-', [status(thm)], ['43', '93'])).
% 0.71/0.92  thf('95', plain, ((v1_funct_1 @ sk_D)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('96', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('97', plain,
% 0.71/0.92      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.71/0.92         ((v1_relat_1 @ X6)
% 0.71/0.92          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.71/0.92      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.71/0.92  thf('98', plain, ((v1_relat_1 @ sk_D)),
% 0.71/0.92      inference('sup-', [status(thm)], ['96', '97'])).
% 0.71/0.92  thf('99', plain,
% 0.71/0.92      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 0.71/0.92        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A))
% 0.71/0.92        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.71/0.92      inference('demod', [status(thm)], ['94', '95', '98'])).
% 0.71/0.92  thf('100', plain,
% 0.71/0.92      ((((sk_D) = (k2_funct_1 @ sk_C))
% 0.71/0.92        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A)))),
% 0.71/0.92      inference('simplify', [status(thm)], ['99'])).
% 0.71/0.92  thf('101', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('102', plain, (((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A))),
% 0.71/0.92      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 0.71/0.92  thf('103', plain, ($false),
% 0.71/0.92      inference('simplify_reflect-', [status(thm)], ['29', '102'])).
% 0.71/0.92  
% 0.71/0.92  % SZS output end Refutation
% 0.71/0.92  
% 0.71/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
