%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jYmU3eonyl

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:43 EST 2020

% Result     : Theorem 2.67s
% Output     : Refutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 168 expanded)
%              Number of leaves         :   36 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  864 (3407 expanded)
%              Number of equality atoms :   58 ( 249 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k9_relat_1 @ X5 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

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

thf('1',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 )
        = ( k5_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['1','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('21',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['11','23'])).

thf('25',plain,
    ( ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
     != sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['0','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('28',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['28','29'])).

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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ( X15
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
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

thf('41',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['33','40','43'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X4: $i] :
      ( ( ( k9_relat_1 @ X4 @ ( k1_relat_1 @ X4 ) )
        = ( k2_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('46',plain,
    ( ( ( k9_relat_1 @ sk_E @ sk_B )
      = ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('49',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('56',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k9_relat_1 @ sk_E @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['46','51','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('62',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['54','55'])).

thf('64',plain,(
    sk_C != sk_C ),
    inference(demod,[status(thm)],['25','30','57','62','63'])).

thf('65',plain,(
    $false ),
    inference(simplify,[status(thm)],['64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jYmU3eonyl
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:51:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.67/2.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.67/2.86  % Solved by: fo/fo7.sh
% 2.67/2.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.67/2.86  % done 804 iterations in 2.402s
% 2.67/2.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.67/2.86  % SZS output start Refutation
% 2.67/2.86  thf(sk_A_type, type, sk_A: $i).
% 2.67/2.86  thf(sk_B_type, type, sk_B: $i).
% 2.67/2.86  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.67/2.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.67/2.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.67/2.86  thf(sk_C_type, type, sk_C: $i).
% 2.67/2.86  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.67/2.86  thf(sk_D_type, type, sk_D: $i).
% 2.67/2.86  thf(sk_E_type, type, sk_E: $i).
% 2.67/2.86  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.67/2.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.67/2.86  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.67/2.86  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.67/2.86  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.67/2.86  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.67/2.86  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.67/2.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.67/2.86  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.67/2.86  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.67/2.86  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.67/2.86  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.67/2.86  thf(t160_relat_1, axiom,
% 2.67/2.86    (![A:$i]:
% 2.67/2.86     ( ( v1_relat_1 @ A ) =>
% 2.67/2.86       ( ![B:$i]:
% 2.67/2.86         ( ( v1_relat_1 @ B ) =>
% 2.67/2.86           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.67/2.86             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.67/2.86  thf('0', plain,
% 2.67/2.86      (![X5 : $i, X6 : $i]:
% 2.67/2.86         (~ (v1_relat_1 @ X5)
% 2.67/2.86          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 2.67/2.86              = (k9_relat_1 @ X5 @ (k2_relat_1 @ X6)))
% 2.67/2.86          | ~ (v1_relat_1 @ X6))),
% 2.67/2.86      inference('cnf', [status(esa)], [t160_relat_1])).
% 2.67/2.86  thf(t20_funct_2, conjecture,
% 2.67/2.86    (![A:$i,B:$i,C:$i,D:$i]:
% 2.67/2.86     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.67/2.86         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.67/2.86       ( ![E:$i]:
% 2.67/2.86         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.67/2.86             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.67/2.86           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.67/2.86               ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 2.67/2.86             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.67/2.86               ( ( k2_relset_1 @
% 2.67/2.86                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.67/2.86                 ( C ) ) ) ) ) ) ))).
% 2.67/2.86  thf(zf_stmt_0, negated_conjecture,
% 2.67/2.86    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.67/2.86        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.67/2.86            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.67/2.86          ( ![E:$i]:
% 2.67/2.86            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.67/2.86                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.67/2.86              ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.67/2.86                  ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 2.67/2.86                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.67/2.86                  ( ( k2_relset_1 @
% 2.67/2.86                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.67/2.86                    ( C ) ) ) ) ) ) ) )),
% 2.67/2.86    inference('cnf.neg', [status(esa)], [t20_funct_2])).
% 2.67/2.86  thf('1', plain,
% 2.67/2.86      (((k2_relset_1 @ sk_A @ sk_C @ 
% 2.67/2.86         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) != (sk_C))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf('2', plain,
% 2.67/2.86      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf('3', plain,
% 2.67/2.86      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf(redefinition_k1_partfun1, axiom,
% 2.67/2.86    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.67/2.86     ( ( ( v1_funct_1 @ E ) & 
% 2.67/2.86         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.67/2.86         ( v1_funct_1 @ F ) & 
% 2.67/2.86         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.67/2.86       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.67/2.86  thf('4', plain,
% 2.67/2.86      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.67/2.86         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 2.67/2.86          | ~ (v1_funct_1 @ X27)
% 2.67/2.86          | ~ (v1_funct_1 @ X30)
% 2.67/2.86          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.67/2.86          | ((k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30)
% 2.67/2.86              = (k5_relat_1 @ X27 @ X30)))),
% 2.67/2.86      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.67/2.86  thf('5', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.86         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.67/2.86            = (k5_relat_1 @ sk_D @ X0))
% 2.67/2.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.67/2.86          | ~ (v1_funct_1 @ X0)
% 2.67/2.86          | ~ (v1_funct_1 @ sk_D))),
% 2.67/2.86      inference('sup-', [status(thm)], ['3', '4'])).
% 2.67/2.86  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf('7', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.86         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.67/2.86            = (k5_relat_1 @ sk_D @ X0))
% 2.67/2.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.67/2.86          | ~ (v1_funct_1 @ X0))),
% 2.67/2.86      inference('demod', [status(thm)], ['5', '6'])).
% 2.67/2.86  thf('8', plain,
% 2.67/2.86      ((~ (v1_funct_1 @ sk_E)
% 2.67/2.86        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.67/2.86            = (k5_relat_1 @ sk_D @ sk_E)))),
% 2.67/2.86      inference('sup-', [status(thm)], ['2', '7'])).
% 2.67/2.86  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf('10', plain,
% 2.67/2.86      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.67/2.86         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.67/2.86      inference('demod', [status(thm)], ['8', '9'])).
% 2.67/2.86  thf('11', plain,
% 2.67/2.86      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 2.67/2.86      inference('demod', [status(thm)], ['1', '10'])).
% 2.67/2.86  thf('12', plain,
% 2.67/2.86      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf('13', plain,
% 2.67/2.86      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf(dt_k1_partfun1, axiom,
% 2.67/2.86    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.67/2.86     ( ( ( v1_funct_1 @ E ) & 
% 2.67/2.86         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.67/2.86         ( v1_funct_1 @ F ) & 
% 2.67/2.86         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.67/2.86       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.67/2.86         ( m1_subset_1 @
% 2.67/2.86           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.67/2.86           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.67/2.86  thf('14', plain,
% 2.67/2.86      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 2.67/2.86         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 2.67/2.86          | ~ (v1_funct_1 @ X21)
% 2.67/2.86          | ~ (v1_funct_1 @ X24)
% 2.67/2.86          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 2.67/2.86          | (m1_subset_1 @ (k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24) @ 
% 2.67/2.86             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X26))))),
% 2.67/2.86      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.67/2.86  thf('15', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.86         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 2.67/2.86           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.67/2.86          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.67/2.86          | ~ (v1_funct_1 @ X1)
% 2.67/2.86          | ~ (v1_funct_1 @ sk_D))),
% 2.67/2.86      inference('sup-', [status(thm)], ['13', '14'])).
% 2.67/2.86  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf('17', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.86         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 2.67/2.86           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.67/2.86          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.67/2.86          | ~ (v1_funct_1 @ X1))),
% 2.67/2.86      inference('demod', [status(thm)], ['15', '16'])).
% 2.67/2.86  thf('18', plain,
% 2.67/2.86      ((~ (v1_funct_1 @ sk_E)
% 2.67/2.86        | (m1_subset_1 @ 
% 2.67/2.86           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 2.67/2.86           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 2.67/2.86      inference('sup-', [status(thm)], ['12', '17'])).
% 2.67/2.86  thf('19', plain, ((v1_funct_1 @ sk_E)),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf('20', plain,
% 2.67/2.86      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.67/2.86         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.67/2.86      inference('demod', [status(thm)], ['8', '9'])).
% 2.67/2.86  thf('21', plain,
% 2.67/2.86      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 2.67/2.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.67/2.86      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.67/2.86  thf(redefinition_k2_relset_1, axiom,
% 2.67/2.86    (![A:$i,B:$i,C:$i]:
% 2.67/2.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.67/2.86       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.67/2.86  thf('22', plain,
% 2.67/2.86      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.67/2.86         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 2.67/2.86          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 2.67/2.86      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.67/2.86  thf('23', plain,
% 2.67/2.86      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 2.67/2.86         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 2.67/2.86      inference('sup-', [status(thm)], ['21', '22'])).
% 2.67/2.86  thf('24', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 2.67/2.86      inference('demod', [status(thm)], ['11', '23'])).
% 2.67/2.86  thf('25', plain,
% 2.67/2.86      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) != (sk_C))
% 2.67/2.86        | ~ (v1_relat_1 @ sk_D)
% 2.67/2.86        | ~ (v1_relat_1 @ sk_E))),
% 2.67/2.86      inference('sup-', [status(thm)], ['0', '24'])).
% 2.67/2.86  thf('26', plain,
% 2.67/2.86      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf('27', plain,
% 2.67/2.86      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.67/2.86         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 2.67/2.86          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 2.67/2.86      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.67/2.86  thf('28', plain,
% 2.67/2.86      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.67/2.86      inference('sup-', [status(thm)], ['26', '27'])).
% 2.67/2.86  thf('29', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_B))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf('30', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 2.67/2.86      inference('sup+', [status(thm)], ['28', '29'])).
% 2.67/2.86  thf('31', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf(d1_funct_2, axiom,
% 2.67/2.86    (![A:$i,B:$i,C:$i]:
% 2.67/2.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.67/2.86       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.67/2.86           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.67/2.86             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.67/2.86         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.67/2.86           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.67/2.86             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.67/2.86  thf(zf_stmt_1, axiom,
% 2.67/2.86    (![C:$i,B:$i,A:$i]:
% 2.67/2.86     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.67/2.86       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.67/2.86  thf('32', plain,
% 2.67/2.86      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.67/2.86         (~ (v1_funct_2 @ X17 @ X15 @ X16)
% 2.67/2.86          | ((X15) = (k1_relset_1 @ X15 @ X16 @ X17))
% 2.67/2.86          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.67/2.86  thf('33', plain,
% 2.67/2.86      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 2.67/2.86        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 2.67/2.86      inference('sup-', [status(thm)], ['31', '32'])).
% 2.67/2.86  thf(zf_stmt_2, axiom,
% 2.67/2.86    (![B:$i,A:$i]:
% 2.67/2.86     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.67/2.86       ( zip_tseitin_0 @ B @ A ) ))).
% 2.67/2.86  thf('34', plain,
% 2.67/2.86      (![X13 : $i, X14 : $i]:
% 2.67/2.86         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.67/2.86  thf('35', plain,
% 2.67/2.86      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.67/2.86  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.67/2.86  thf(zf_stmt_5, axiom,
% 2.67/2.86    (![A:$i,B:$i,C:$i]:
% 2.67/2.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.67/2.86       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.67/2.86         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.67/2.86           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.67/2.86             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.67/2.86  thf('36', plain,
% 2.67/2.86      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.67/2.86         (~ (zip_tseitin_0 @ X18 @ X19)
% 2.67/2.86          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 2.67/2.86          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.67/2.86  thf('37', plain,
% 2.67/2.86      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 2.67/2.86      inference('sup-', [status(thm)], ['35', '36'])).
% 2.67/2.86  thf('38', plain,
% 2.67/2.86      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 2.67/2.86      inference('sup-', [status(thm)], ['34', '37'])).
% 2.67/2.86  thf('39', plain, (((sk_C) != (k1_xboole_0))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf('40', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 2.67/2.86      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 2.67/2.86  thf('41', plain,
% 2.67/2.86      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf(redefinition_k1_relset_1, axiom,
% 2.67/2.86    (![A:$i,B:$i,C:$i]:
% 2.67/2.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.67/2.86       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.67/2.86  thf('42', plain,
% 2.67/2.86      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.67/2.86         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 2.67/2.86          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 2.67/2.86      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.67/2.86  thf('43', plain,
% 2.67/2.86      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 2.67/2.86      inference('sup-', [status(thm)], ['41', '42'])).
% 2.67/2.86  thf('44', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 2.67/2.86      inference('demod', [status(thm)], ['33', '40', '43'])).
% 2.67/2.86  thf(t146_relat_1, axiom,
% 2.67/2.86    (![A:$i]:
% 2.67/2.86     ( ( v1_relat_1 @ A ) =>
% 2.67/2.86       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 2.67/2.86  thf('45', plain,
% 2.67/2.86      (![X4 : $i]:
% 2.67/2.86         (((k9_relat_1 @ X4 @ (k1_relat_1 @ X4)) = (k2_relat_1 @ X4))
% 2.67/2.86          | ~ (v1_relat_1 @ X4))),
% 2.67/2.86      inference('cnf', [status(esa)], [t146_relat_1])).
% 2.67/2.86  thf('46', plain,
% 2.67/2.86      ((((k9_relat_1 @ sk_E @ sk_B) = (k2_relat_1 @ sk_E))
% 2.67/2.86        | ~ (v1_relat_1 @ sk_E))),
% 2.67/2.86      inference('sup+', [status(thm)], ['44', '45'])).
% 2.67/2.86  thf('47', plain,
% 2.67/2.86      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf('48', plain,
% 2.67/2.86      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.67/2.86         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 2.67/2.86          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 2.67/2.86      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.67/2.86  thf('49', plain,
% 2.67/2.86      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 2.67/2.86      inference('sup-', [status(thm)], ['47', '48'])).
% 2.67/2.86  thf('50', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_C))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf('51', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 2.67/2.86      inference('sup+', [status(thm)], ['49', '50'])).
% 2.67/2.86  thf('52', plain,
% 2.67/2.86      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf(cc2_relat_1, axiom,
% 2.67/2.86    (![A:$i]:
% 2.67/2.86     ( ( v1_relat_1 @ A ) =>
% 2.67/2.86       ( ![B:$i]:
% 2.67/2.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.67/2.86  thf('53', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.67/2.86          | (v1_relat_1 @ X0)
% 2.67/2.86          | ~ (v1_relat_1 @ X1))),
% 2.67/2.86      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.67/2.86  thf('54', plain,
% 2.67/2.86      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 2.67/2.86      inference('sup-', [status(thm)], ['52', '53'])).
% 2.67/2.86  thf(fc6_relat_1, axiom,
% 2.67/2.86    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.67/2.86  thf('55', plain,
% 2.67/2.86      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.67/2.86      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.67/2.86  thf('56', plain, ((v1_relat_1 @ sk_E)),
% 2.67/2.86      inference('demod', [status(thm)], ['54', '55'])).
% 2.67/2.86  thf('57', plain, (((k9_relat_1 @ sk_E @ sk_B) = (sk_C))),
% 2.67/2.86      inference('demod', [status(thm)], ['46', '51', '56'])).
% 2.67/2.86  thf('58', plain,
% 2.67/2.86      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf('59', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.67/2.86          | (v1_relat_1 @ X0)
% 2.67/2.86          | ~ (v1_relat_1 @ X1))),
% 2.67/2.86      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.67/2.86  thf('60', plain,
% 2.67/2.86      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 2.67/2.86      inference('sup-', [status(thm)], ['58', '59'])).
% 2.67/2.86  thf('61', plain,
% 2.67/2.86      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.67/2.86      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.67/2.86  thf('62', plain, ((v1_relat_1 @ sk_D)),
% 2.67/2.86      inference('demod', [status(thm)], ['60', '61'])).
% 2.67/2.86  thf('63', plain, ((v1_relat_1 @ sk_E)),
% 2.67/2.86      inference('demod', [status(thm)], ['54', '55'])).
% 2.67/2.86  thf('64', plain, (((sk_C) != (sk_C))),
% 2.67/2.86      inference('demod', [status(thm)], ['25', '30', '57', '62', '63'])).
% 2.67/2.86  thf('65', plain, ($false), inference('simplify', [status(thm)], ['64'])).
% 2.67/2.86  
% 2.67/2.86  % SZS output end Refutation
% 2.67/2.86  
% 2.67/2.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
