%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u3Mk7gUQOS

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:41 EST 2020

% Result     : Theorem 2.42s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 159 expanded)
%              Number of leaves         :   35 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  840 (3365 expanded)
%              Number of equality atoms :   58 ( 249 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X25 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('53',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('54',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k9_relat_1 @ sk_E @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['46','51','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('58',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['52','53'])).

thf('60',plain,(
    sk_C != sk_C ),
    inference(demod,[status(thm)],['25','30','55','58','59'])).

thf('61',plain,(
    $false ),
    inference(simplify,[status(thm)],['60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u3Mk7gUQOS
% 0.14/0.36  % Computer   : n021.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 19:42:05 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 2.42/2.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.42/2.60  % Solved by: fo/fo7.sh
% 2.42/2.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.42/2.60  % done 804 iterations in 2.122s
% 2.42/2.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.42/2.60  % SZS output start Refutation
% 2.42/2.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.42/2.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.42/2.60  thf(sk_D_type, type, sk_D: $i).
% 2.42/2.60  thf(sk_E_type, type, sk_E: $i).
% 2.42/2.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.42/2.60  thf(sk_B_type, type, sk_B: $i).
% 2.42/2.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.42/2.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.42/2.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.42/2.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.42/2.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.42/2.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.42/2.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.42/2.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.42/2.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.42/2.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.42/2.60  thf(sk_A_type, type, sk_A: $i).
% 2.42/2.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.42/2.60  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.42/2.60  thf(sk_C_type, type, sk_C: $i).
% 2.42/2.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.42/2.60  thf(t160_relat_1, axiom,
% 2.42/2.60    (![A:$i]:
% 2.42/2.60     ( ( v1_relat_1 @ A ) =>
% 2.42/2.60       ( ![B:$i]:
% 2.42/2.60         ( ( v1_relat_1 @ B ) =>
% 2.42/2.60           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.42/2.60             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.42/2.60  thf('0', plain,
% 2.42/2.60      (![X1 : $i, X2 : $i]:
% 2.42/2.60         (~ (v1_relat_1 @ X1)
% 2.42/2.60          | ((k2_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 2.42/2.60              = (k9_relat_1 @ X1 @ (k2_relat_1 @ X2)))
% 2.42/2.60          | ~ (v1_relat_1 @ X2))),
% 2.42/2.60      inference('cnf', [status(esa)], [t160_relat_1])).
% 2.42/2.60  thf(t20_funct_2, conjecture,
% 2.42/2.60    (![A:$i,B:$i,C:$i,D:$i]:
% 2.42/2.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.42/2.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.42/2.60       ( ![E:$i]:
% 2.42/2.60         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.42/2.60             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.42/2.60           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.42/2.60               ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 2.42/2.60             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.42/2.60               ( ( k2_relset_1 @
% 2.42/2.60                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.42/2.60                 ( C ) ) ) ) ) ) ))).
% 2.42/2.60  thf(zf_stmt_0, negated_conjecture,
% 2.42/2.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.42/2.60        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.42/2.60            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.42/2.60          ( ![E:$i]:
% 2.42/2.60            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.42/2.60                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.42/2.60              ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.42/2.60                  ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 2.42/2.60                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.42/2.60                  ( ( k2_relset_1 @
% 2.42/2.60                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.42/2.60                    ( C ) ) ) ) ) ) ) )),
% 2.42/2.60    inference('cnf.neg', [status(esa)], [t20_funct_2])).
% 2.42/2.60  thf('1', plain,
% 2.42/2.60      (((k2_relset_1 @ sk_A @ sk_C @ 
% 2.42/2.60         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) != (sk_C))),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf('2', plain,
% 2.42/2.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf('3', plain,
% 2.42/2.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf(redefinition_k1_partfun1, axiom,
% 2.42/2.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.42/2.60     ( ( ( v1_funct_1 @ E ) & 
% 2.42/2.60         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.42/2.60         ( v1_funct_1 @ F ) & 
% 2.42/2.60         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.42/2.60       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.42/2.60  thf('4', plain,
% 2.42/2.60      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.42/2.60         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 2.42/2.60          | ~ (v1_funct_1 @ X26)
% 2.42/2.60          | ~ (v1_funct_1 @ X29)
% 2.42/2.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.42/2.60          | ((k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 2.42/2.60              = (k5_relat_1 @ X26 @ X29)))),
% 2.42/2.60      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.42/2.60  thf('5', plain,
% 2.42/2.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.60         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.42/2.60            = (k5_relat_1 @ sk_D @ X0))
% 2.42/2.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.42/2.60          | ~ (v1_funct_1 @ X0)
% 2.42/2.60          | ~ (v1_funct_1 @ sk_D))),
% 2.42/2.60      inference('sup-', [status(thm)], ['3', '4'])).
% 2.42/2.60  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf('7', plain,
% 2.42/2.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.60         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.42/2.60            = (k5_relat_1 @ sk_D @ X0))
% 2.42/2.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.42/2.60          | ~ (v1_funct_1 @ X0))),
% 2.42/2.60      inference('demod', [status(thm)], ['5', '6'])).
% 2.42/2.60  thf('8', plain,
% 2.42/2.60      ((~ (v1_funct_1 @ sk_E)
% 2.42/2.60        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.42/2.60            = (k5_relat_1 @ sk_D @ sk_E)))),
% 2.42/2.60      inference('sup-', [status(thm)], ['2', '7'])).
% 2.42/2.60  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf('10', plain,
% 2.42/2.60      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.42/2.60         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.42/2.60      inference('demod', [status(thm)], ['8', '9'])).
% 2.42/2.60  thf('11', plain,
% 2.42/2.60      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 2.42/2.60      inference('demod', [status(thm)], ['1', '10'])).
% 2.42/2.60  thf('12', plain,
% 2.42/2.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf('13', plain,
% 2.42/2.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf(dt_k1_partfun1, axiom,
% 2.42/2.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.42/2.60     ( ( ( v1_funct_1 @ E ) & 
% 2.42/2.60         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.42/2.60         ( v1_funct_1 @ F ) & 
% 2.42/2.60         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.42/2.60       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.42/2.60         ( m1_subset_1 @
% 2.42/2.60           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.42/2.60           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.42/2.60  thf('14', plain,
% 2.42/2.60      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.42/2.60         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 2.42/2.60          | ~ (v1_funct_1 @ X20)
% 2.42/2.60          | ~ (v1_funct_1 @ X23)
% 2.42/2.60          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 2.42/2.60          | (m1_subset_1 @ (k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23) @ 
% 2.42/2.60             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X25))))),
% 2.42/2.60      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.42/2.60  thf('15', plain,
% 2.42/2.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.60         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 2.42/2.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.42/2.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.42/2.60          | ~ (v1_funct_1 @ X1)
% 2.42/2.60          | ~ (v1_funct_1 @ sk_D))),
% 2.42/2.60      inference('sup-', [status(thm)], ['13', '14'])).
% 2.42/2.60  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf('17', plain,
% 2.42/2.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.60         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 2.42/2.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.42/2.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.42/2.60          | ~ (v1_funct_1 @ X1))),
% 2.42/2.60      inference('demod', [status(thm)], ['15', '16'])).
% 2.42/2.60  thf('18', plain,
% 2.42/2.60      ((~ (v1_funct_1 @ sk_E)
% 2.42/2.60        | (m1_subset_1 @ 
% 2.42/2.60           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 2.42/2.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 2.42/2.60      inference('sup-', [status(thm)], ['12', '17'])).
% 2.42/2.60  thf('19', plain, ((v1_funct_1 @ sk_E)),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf('20', plain,
% 2.42/2.60      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.42/2.60         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.42/2.60      inference('demod', [status(thm)], ['8', '9'])).
% 2.42/2.60  thf('21', plain,
% 2.42/2.60      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 2.42/2.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.42/2.60      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.42/2.60  thf(redefinition_k2_relset_1, axiom,
% 2.42/2.60    (![A:$i,B:$i,C:$i]:
% 2.42/2.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.42/2.60       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.42/2.60  thf('22', plain,
% 2.42/2.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.42/2.60         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 2.42/2.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.42/2.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.42/2.60  thf('23', plain,
% 2.42/2.60      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 2.42/2.60         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 2.42/2.60      inference('sup-', [status(thm)], ['21', '22'])).
% 2.42/2.60  thf('24', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 2.42/2.60      inference('demod', [status(thm)], ['11', '23'])).
% 2.42/2.60  thf('25', plain,
% 2.42/2.60      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) != (sk_C))
% 2.42/2.60        | ~ (v1_relat_1 @ sk_D)
% 2.42/2.60        | ~ (v1_relat_1 @ sk_E))),
% 2.42/2.60      inference('sup-', [status(thm)], ['0', '24'])).
% 2.42/2.60  thf('26', plain,
% 2.42/2.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf('27', plain,
% 2.42/2.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.42/2.60         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 2.42/2.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.42/2.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.42/2.60  thf('28', plain,
% 2.42/2.60      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.42/2.60      inference('sup-', [status(thm)], ['26', '27'])).
% 2.42/2.60  thf('29', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_B))),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf('30', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 2.42/2.60      inference('sup+', [status(thm)], ['28', '29'])).
% 2.42/2.60  thf('31', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf(d1_funct_2, axiom,
% 2.42/2.60    (![A:$i,B:$i,C:$i]:
% 2.42/2.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.42/2.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.42/2.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.42/2.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.42/2.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.42/2.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.42/2.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.42/2.60  thf(zf_stmt_1, axiom,
% 2.42/2.60    (![C:$i,B:$i,A:$i]:
% 2.42/2.60     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.42/2.60       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.42/2.60  thf('32', plain,
% 2.42/2.60      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.42/2.60         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 2.42/2.60          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 2.42/2.60          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.42/2.60  thf('33', plain,
% 2.42/2.60      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 2.42/2.60        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 2.42/2.60      inference('sup-', [status(thm)], ['31', '32'])).
% 2.42/2.60  thf(zf_stmt_2, axiom,
% 2.42/2.60    (![B:$i,A:$i]:
% 2.42/2.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.42/2.60       ( zip_tseitin_0 @ B @ A ) ))).
% 2.42/2.60  thf('34', plain,
% 2.42/2.60      (![X12 : $i, X13 : $i]:
% 2.42/2.60         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.42/2.60  thf('35', plain,
% 2.42/2.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.42/2.60  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.42/2.60  thf(zf_stmt_5, axiom,
% 2.42/2.60    (![A:$i,B:$i,C:$i]:
% 2.42/2.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.42/2.60       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.42/2.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.42/2.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.42/2.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.42/2.60  thf('36', plain,
% 2.42/2.60      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.42/2.60         (~ (zip_tseitin_0 @ X17 @ X18)
% 2.42/2.60          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 2.42/2.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.42/2.60  thf('37', plain,
% 2.42/2.60      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 2.42/2.60      inference('sup-', [status(thm)], ['35', '36'])).
% 2.42/2.60  thf('38', plain,
% 2.42/2.60      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 2.42/2.60      inference('sup-', [status(thm)], ['34', '37'])).
% 2.42/2.60  thf('39', plain, (((sk_C) != (k1_xboole_0))),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf('40', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 2.42/2.60      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 2.42/2.60  thf('41', plain,
% 2.42/2.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf(redefinition_k1_relset_1, axiom,
% 2.42/2.60    (![A:$i,B:$i,C:$i]:
% 2.42/2.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.42/2.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.42/2.60  thf('42', plain,
% 2.42/2.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.42/2.60         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 2.42/2.60          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.42/2.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.42/2.60  thf('43', plain,
% 2.42/2.60      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 2.42/2.60      inference('sup-', [status(thm)], ['41', '42'])).
% 2.42/2.60  thf('44', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 2.42/2.60      inference('demod', [status(thm)], ['33', '40', '43'])).
% 2.42/2.60  thf(t146_relat_1, axiom,
% 2.42/2.60    (![A:$i]:
% 2.42/2.60     ( ( v1_relat_1 @ A ) =>
% 2.42/2.60       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 2.42/2.60  thf('45', plain,
% 2.42/2.60      (![X0 : $i]:
% 2.42/2.60         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 2.42/2.60          | ~ (v1_relat_1 @ X0))),
% 2.42/2.60      inference('cnf', [status(esa)], [t146_relat_1])).
% 2.42/2.60  thf('46', plain,
% 2.42/2.60      ((((k9_relat_1 @ sk_E @ sk_B) = (k2_relat_1 @ sk_E))
% 2.42/2.60        | ~ (v1_relat_1 @ sk_E))),
% 2.42/2.60      inference('sup+', [status(thm)], ['44', '45'])).
% 2.42/2.60  thf('47', plain,
% 2.42/2.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf('48', plain,
% 2.42/2.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.42/2.60         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 2.42/2.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.42/2.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.42/2.60  thf('49', plain,
% 2.42/2.60      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 2.42/2.60      inference('sup-', [status(thm)], ['47', '48'])).
% 2.42/2.60  thf('50', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_C))),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf('51', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 2.42/2.60      inference('sup+', [status(thm)], ['49', '50'])).
% 2.42/2.60  thf('52', plain,
% 2.42/2.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf(cc1_relset_1, axiom,
% 2.42/2.60    (![A:$i,B:$i,C:$i]:
% 2.42/2.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.42/2.60       ( v1_relat_1 @ C ) ))).
% 2.42/2.60  thf('53', plain,
% 2.42/2.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.42/2.60         ((v1_relat_1 @ X3)
% 2.42/2.60          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 2.42/2.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.42/2.60  thf('54', plain, ((v1_relat_1 @ sk_E)),
% 2.42/2.60      inference('sup-', [status(thm)], ['52', '53'])).
% 2.42/2.60  thf('55', plain, (((k9_relat_1 @ sk_E @ sk_B) = (sk_C))),
% 2.42/2.60      inference('demod', [status(thm)], ['46', '51', '54'])).
% 2.42/2.60  thf('56', plain,
% 2.42/2.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.42/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.60  thf('57', plain,
% 2.42/2.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.42/2.60         ((v1_relat_1 @ X3)
% 2.42/2.60          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 2.42/2.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.42/2.60  thf('58', plain, ((v1_relat_1 @ sk_D)),
% 2.42/2.60      inference('sup-', [status(thm)], ['56', '57'])).
% 2.42/2.60  thf('59', plain, ((v1_relat_1 @ sk_E)),
% 2.42/2.60      inference('sup-', [status(thm)], ['52', '53'])).
% 2.42/2.60  thf('60', plain, (((sk_C) != (sk_C))),
% 2.42/2.60      inference('demod', [status(thm)], ['25', '30', '55', '58', '59'])).
% 2.42/2.60  thf('61', plain, ($false), inference('simplify', [status(thm)], ['60'])).
% 2.42/2.60  
% 2.42/2.60  % SZS output end Refutation
% 2.42/2.60  
% 2.42/2.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
