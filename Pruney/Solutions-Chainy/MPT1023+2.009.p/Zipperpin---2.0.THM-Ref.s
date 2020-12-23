%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aVXVZzE9x7

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:29 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 508 expanded)
%              Number of leaves         :   38 ( 165 expanded)
%              Depth                    :   22
%              Number of atoms          : 1060 (7955 expanded)
%              Number of equality atoms :   80 ( 342 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t113_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( m1_subset_1 @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['2'])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['1','3'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X16 ) ) )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('15',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_1 = X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X16 ) ) )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['28','37'])).

thf('39',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['1','3'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('43',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_1 = X0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('47',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('50',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['39','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('57',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('58',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['55','60'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X12 = X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( ( k1_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('65',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('66',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['55','60'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','66','67','68'])).

thf('70',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('73',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['70','73','74'])).

thf('76',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['75'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('78',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['77'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('79',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('81',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_C_1 = sk_D )
    | ( m1_subset_1 @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['76','82'])).

thf('84',plain,(
    ! [X34: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X34 )
        = ( k1_funct_1 @ sk_D @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['85'])).

thf('87',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X12 = X11 )
      | ( ( k1_funct_1 @ X12 @ ( sk_C @ X11 @ X12 ) )
       != ( k1_funct_1 @ X11 @ ( sk_C @ X11 @ X12 ) ) )
      | ( ( k1_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('88',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('90',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['55','60'])).

thf('92',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['28','37'])).

thf('93',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('95',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['88','89','90','91','92','93','94'])).

thf('96',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['2'])).

thf('99',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['0','96','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aVXVZzE9x7
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:26:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 2.13/2.33  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.13/2.33  % Solved by: fo/fo7.sh
% 2.13/2.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.13/2.33  % done 1644 iterations in 1.881s
% 2.13/2.33  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.13/2.33  % SZS output start Refutation
% 2.13/2.33  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.13/2.33  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.13/2.33  thf(sk_B_type, type, sk_B: $i).
% 2.13/2.33  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.13/2.33  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.13/2.33  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.13/2.33  thf(sk_D_type, type, sk_D: $i).
% 2.13/2.33  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.13/2.33  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.13/2.33  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.13/2.33  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.13/2.33  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.13/2.33  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.13/2.33  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.13/2.33  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.13/2.33  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.13/2.33  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.13/2.33  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.13/2.33  thf(sk_A_type, type, sk_A: $i).
% 2.13/2.33  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.13/2.33  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.13/2.33  thf(t113_funct_2, conjecture,
% 2.13/2.33    (![A:$i,B:$i,C:$i]:
% 2.13/2.33     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.13/2.33         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.13/2.33       ( ![D:$i]:
% 2.13/2.33         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.13/2.33             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.13/2.33           ( ( ![E:$i]:
% 2.13/2.33               ( ( m1_subset_1 @ E @ A ) =>
% 2.13/2.33                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 2.13/2.33             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 2.13/2.33  thf(zf_stmt_0, negated_conjecture,
% 2.13/2.33    (~( ![A:$i,B:$i,C:$i]:
% 2.13/2.33        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.13/2.33            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.13/2.33          ( ![D:$i]:
% 2.13/2.33            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.13/2.33                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.13/2.33              ( ( ![E:$i]:
% 2.13/2.33                  ( ( m1_subset_1 @ E @ A ) =>
% 2.13/2.33                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 2.13/2.33                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 2.13/2.33    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 2.13/2.33  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf('1', plain,
% 2.13/2.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf(reflexivity_r2_relset_1, axiom,
% 2.13/2.33    (![A:$i,B:$i,C:$i,D:$i]:
% 2.13/2.33     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.13/2.33         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.13/2.33       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 2.13/2.33  thf('2', plain,
% 2.13/2.33      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.13/2.33         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 2.13/2.33          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 2.13/2.33          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 2.13/2.33      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 2.13/2.33  thf('3', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.33         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 2.13/2.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 2.13/2.33      inference('condensation', [status(thm)], ['2'])).
% 2.13/2.33  thf('4', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 2.13/2.33      inference('sup-', [status(thm)], ['1', '3'])).
% 2.13/2.33  thf(d1_funct_2, axiom,
% 2.13/2.33    (![A:$i,B:$i,C:$i]:
% 2.13/2.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.13/2.33       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.13/2.33           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.13/2.33             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.13/2.33         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.13/2.33           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.13/2.33             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.13/2.33  thf(zf_stmt_1, axiom,
% 2.13/2.33    (![B:$i,A:$i]:
% 2.13/2.33     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.13/2.33       ( zip_tseitin_0 @ B @ A ) ))).
% 2.13/2.33  thf('5', plain,
% 2.13/2.33      (![X26 : $i, X27 : $i]:
% 2.13/2.33         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.13/2.33  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.13/2.33  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.13/2.33      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.13/2.33  thf('7', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 2.13/2.33      inference('sup+', [status(thm)], ['5', '6'])).
% 2.13/2.33  thf('8', plain,
% 2.13/2.33      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf(cc4_relset_1, axiom,
% 2.13/2.33    (![A:$i,B:$i]:
% 2.13/2.33     ( ( v1_xboole_0 @ A ) =>
% 2.13/2.33       ( ![C:$i]:
% 2.13/2.33         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 2.13/2.33           ( v1_xboole_0 @ C ) ) ) ))).
% 2.13/2.33  thf('9', plain,
% 2.13/2.33      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.13/2.33         (~ (v1_xboole_0 @ X16)
% 2.13/2.33          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X16)))
% 2.13/2.33          | (v1_xboole_0 @ X17))),
% 2.13/2.33      inference('cnf', [status(esa)], [cc4_relset_1])).
% 2.13/2.33  thf('10', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_B))),
% 2.13/2.33      inference('sup-', [status(thm)], ['8', '9'])).
% 2.13/2.33  thf('11', plain,
% 2.13/2.33      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C_1))),
% 2.13/2.33      inference('sup-', [status(thm)], ['7', '10'])).
% 2.13/2.33  thf(t8_boole, axiom,
% 2.13/2.33    (![A:$i,B:$i]:
% 2.13/2.33     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.13/2.33  thf('12', plain,
% 2.13/2.33      (![X3 : $i, X4 : $i]:
% 2.13/2.33         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 2.13/2.33      inference('cnf', [status(esa)], [t8_boole])).
% 2.13/2.33  thf('13', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i]:
% 2.13/2.33         ((zip_tseitin_0 @ sk_B @ X1)
% 2.13/2.33          | ((sk_C_1) = (X0))
% 2.13/2.33          | ~ (v1_xboole_0 @ X0))),
% 2.13/2.33      inference('sup-', [status(thm)], ['11', '12'])).
% 2.13/2.33  thf('14', plain,
% 2.13/2.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.13/2.33  thf(zf_stmt_3, axiom,
% 2.13/2.33    (![C:$i,B:$i,A:$i]:
% 2.13/2.33     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.13/2.33       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.13/2.33  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.13/2.33  thf(zf_stmt_5, axiom,
% 2.13/2.33    (![A:$i,B:$i,C:$i]:
% 2.13/2.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.13/2.33       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.13/2.33         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.13/2.33           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.13/2.33             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.13/2.33  thf('15', plain,
% 2.13/2.33      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.13/2.33         (~ (zip_tseitin_0 @ X31 @ X32)
% 2.13/2.33          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 2.13/2.33          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.13/2.33  thf('16', plain,
% 2.13/2.33      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.13/2.33      inference('sup-', [status(thm)], ['14', '15'])).
% 2.13/2.33  thf('17', plain,
% 2.13/2.33      (![X0 : $i]:
% 2.13/2.33         (~ (v1_xboole_0 @ X0)
% 2.13/2.33          | ((sk_C_1) = (X0))
% 2.13/2.33          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 2.13/2.33      inference('sup-', [status(thm)], ['13', '16'])).
% 2.13/2.33  thf('18', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf('19', plain,
% 2.13/2.33      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.13/2.33         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 2.13/2.33          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 2.13/2.33          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.13/2.33  thf('20', plain,
% 2.13/2.33      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 2.13/2.33        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 2.13/2.33      inference('sup-', [status(thm)], ['18', '19'])).
% 2.13/2.33  thf('21', plain,
% 2.13/2.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf(redefinition_k1_relset_1, axiom,
% 2.13/2.33    (![A:$i,B:$i,C:$i]:
% 2.13/2.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.13/2.33       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.13/2.33  thf('22', plain,
% 2.13/2.33      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.13/2.33         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 2.13/2.33          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 2.13/2.33      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.13/2.33  thf('23', plain,
% 2.13/2.33      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.13/2.33      inference('sup-', [status(thm)], ['21', '22'])).
% 2.13/2.33  thf('24', plain,
% 2.13/2.33      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.13/2.33      inference('demod', [status(thm)], ['20', '23'])).
% 2.13/2.33  thf('25', plain,
% 2.13/2.33      (![X0 : $i]:
% 2.13/2.33         (((sk_C_1) = (X0))
% 2.13/2.33          | ~ (v1_xboole_0 @ X0)
% 2.13/2.33          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.13/2.33      inference('sup-', [status(thm)], ['17', '24'])).
% 2.13/2.33  thf('26', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf('27', plain,
% 2.13/2.33      (![X0 : $i]:
% 2.13/2.33         (~ (r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D)
% 2.13/2.33          | ((sk_A) = (k1_relat_1 @ sk_D))
% 2.13/2.33          | ~ (v1_xboole_0 @ X0))),
% 2.13/2.33      inference('sup-', [status(thm)], ['25', '26'])).
% 2.13/2.33  thf('28', plain, ((~ (v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.13/2.33      inference('sup-', [status(thm)], ['4', '27'])).
% 2.13/2.33  thf('29', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 2.13/2.33      inference('sup+', [status(thm)], ['5', '6'])).
% 2.13/2.33  thf('30', plain,
% 2.13/2.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf('31', plain,
% 2.13/2.33      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.13/2.33         (~ (v1_xboole_0 @ X16)
% 2.13/2.33          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X16)))
% 2.13/2.33          | (v1_xboole_0 @ X17))),
% 2.13/2.33      inference('cnf', [status(esa)], [cc4_relset_1])).
% 2.13/2.33  thf('32', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B))),
% 2.13/2.33      inference('sup-', [status(thm)], ['30', '31'])).
% 2.13/2.33  thf('33', plain,
% 2.13/2.33      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_D))),
% 2.13/2.33      inference('sup-', [status(thm)], ['29', '32'])).
% 2.13/2.33  thf('34', plain,
% 2.13/2.33      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.13/2.33      inference('sup-', [status(thm)], ['14', '15'])).
% 2.13/2.33  thf('35', plain,
% 2.13/2.33      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 2.13/2.33      inference('sup-', [status(thm)], ['33', '34'])).
% 2.13/2.33  thf('36', plain,
% 2.13/2.33      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.13/2.33      inference('demod', [status(thm)], ['20', '23'])).
% 2.13/2.33  thf('37', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.13/2.33      inference('sup-', [status(thm)], ['35', '36'])).
% 2.13/2.33  thf('38', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.13/2.33      inference('clc', [status(thm)], ['28', '37'])).
% 2.13/2.33  thf('39', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 2.13/2.33      inference('sup-', [status(thm)], ['1', '3'])).
% 2.13/2.33  thf('40', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i]:
% 2.13/2.33         ((zip_tseitin_0 @ sk_B @ X1)
% 2.13/2.33          | ((sk_C_1) = (X0))
% 2.13/2.33          | ~ (v1_xboole_0 @ X0))),
% 2.13/2.33      inference('sup-', [status(thm)], ['11', '12'])).
% 2.13/2.33  thf('41', plain,
% 2.13/2.33      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf('42', plain,
% 2.13/2.33      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.13/2.33         (~ (zip_tseitin_0 @ X31 @ X32)
% 2.13/2.33          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 2.13/2.33          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.13/2.33  thf('43', plain,
% 2.13/2.33      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 2.13/2.33        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.13/2.33      inference('sup-', [status(thm)], ['41', '42'])).
% 2.13/2.33  thf('44', plain,
% 2.13/2.33      (![X0 : $i]:
% 2.13/2.33         (~ (v1_xboole_0 @ X0)
% 2.13/2.33          | ((sk_C_1) = (X0))
% 2.13/2.33          | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 2.13/2.33      inference('sup-', [status(thm)], ['40', '43'])).
% 2.13/2.33  thf('45', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf('46', plain,
% 2.13/2.33      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.13/2.33         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 2.13/2.33          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 2.13/2.33          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.13/2.33  thf('47', plain,
% 2.13/2.33      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 2.13/2.33        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 2.13/2.33      inference('sup-', [status(thm)], ['45', '46'])).
% 2.13/2.33  thf('48', plain,
% 2.13/2.33      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf('49', plain,
% 2.13/2.33      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.13/2.33         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 2.13/2.33          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 2.13/2.33      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.13/2.33  thf('50', plain,
% 2.13/2.33      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 2.13/2.33      inference('sup-', [status(thm)], ['48', '49'])).
% 2.13/2.33  thf('51', plain,
% 2.13/2.33      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 2.13/2.33        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 2.13/2.33      inference('demod', [status(thm)], ['47', '50'])).
% 2.13/2.33  thf('52', plain,
% 2.13/2.33      (![X0 : $i]:
% 2.13/2.33         (((sk_C_1) = (X0))
% 2.13/2.33          | ~ (v1_xboole_0 @ X0)
% 2.13/2.33          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 2.13/2.33      inference('sup-', [status(thm)], ['44', '51'])).
% 2.13/2.33  thf('53', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf('54', plain,
% 2.13/2.33      (![X0 : $i]:
% 2.13/2.33         (~ (r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D)
% 2.13/2.33          | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 2.13/2.33          | ~ (v1_xboole_0 @ X0))),
% 2.13/2.33      inference('sup-', [status(thm)], ['52', '53'])).
% 2.13/2.33  thf('55', plain,
% 2.13/2.33      ((~ (v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 2.13/2.33      inference('sup-', [status(thm)], ['39', '54'])).
% 2.13/2.33  thf('56', plain,
% 2.13/2.33      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_D))),
% 2.13/2.33      inference('sup-', [status(thm)], ['29', '32'])).
% 2.13/2.33  thf('57', plain,
% 2.13/2.33      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 2.13/2.33        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.13/2.33      inference('sup-', [status(thm)], ['41', '42'])).
% 2.13/2.33  thf('58', plain,
% 2.13/2.33      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 2.13/2.33      inference('sup-', [status(thm)], ['56', '57'])).
% 2.13/2.33  thf('59', plain,
% 2.13/2.33      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 2.13/2.33        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 2.13/2.33      inference('demod', [status(thm)], ['47', '50'])).
% 2.13/2.33  thf('60', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 2.13/2.33      inference('sup-', [status(thm)], ['58', '59'])).
% 2.13/2.33  thf('61', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 2.13/2.33      inference('clc', [status(thm)], ['55', '60'])).
% 2.13/2.33  thf(t9_funct_1, axiom,
% 2.13/2.33    (![A:$i]:
% 2.13/2.33     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.13/2.33       ( ![B:$i]:
% 2.13/2.33         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.13/2.33           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 2.13/2.33               ( ![C:$i]:
% 2.13/2.33                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 2.13/2.33                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 2.13/2.33             ( ( A ) = ( B ) ) ) ) ) ))).
% 2.13/2.33  thf('62', plain,
% 2.13/2.33      (![X11 : $i, X12 : $i]:
% 2.13/2.33         (~ (v1_relat_1 @ X11)
% 2.13/2.33          | ~ (v1_funct_1 @ X11)
% 2.13/2.33          | ((X12) = (X11))
% 2.13/2.33          | (r2_hidden @ (sk_C @ X11 @ X12) @ (k1_relat_1 @ X12))
% 2.13/2.33          | ((k1_relat_1 @ X12) != (k1_relat_1 @ X11))
% 2.13/2.33          | ~ (v1_funct_1 @ X12)
% 2.13/2.33          | ~ (v1_relat_1 @ X12))),
% 2.13/2.33      inference('cnf', [status(esa)], [t9_funct_1])).
% 2.13/2.33  thf('63', plain,
% 2.13/2.33      (![X0 : $i]:
% 2.13/2.33         (((sk_A) != (k1_relat_1 @ X0))
% 2.13/2.33          | ~ (v1_relat_1 @ sk_C_1)
% 2.13/2.33          | ~ (v1_funct_1 @ sk_C_1)
% 2.13/2.33          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 2.13/2.33          | ((sk_C_1) = (X0))
% 2.13/2.33          | ~ (v1_funct_1 @ X0)
% 2.13/2.33          | ~ (v1_relat_1 @ X0))),
% 2.13/2.33      inference('sup-', [status(thm)], ['61', '62'])).
% 2.13/2.33  thf('64', plain,
% 2.13/2.33      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf(cc1_relset_1, axiom,
% 2.13/2.33    (![A:$i,B:$i,C:$i]:
% 2.13/2.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.13/2.33       ( v1_relat_1 @ C ) ))).
% 2.13/2.33  thf('65', plain,
% 2.13/2.33      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.13/2.33         ((v1_relat_1 @ X13)
% 2.13/2.33          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.13/2.33      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.13/2.33  thf('66', plain, ((v1_relat_1 @ sk_C_1)),
% 2.13/2.33      inference('sup-', [status(thm)], ['64', '65'])).
% 2.13/2.33  thf('67', plain, ((v1_funct_1 @ sk_C_1)),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf('68', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 2.13/2.33      inference('clc', [status(thm)], ['55', '60'])).
% 2.13/2.33  thf('69', plain,
% 2.13/2.33      (![X0 : $i]:
% 2.13/2.33         (((sk_A) != (k1_relat_1 @ X0))
% 2.13/2.33          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 2.13/2.33          | ((sk_C_1) = (X0))
% 2.13/2.33          | ~ (v1_funct_1 @ X0)
% 2.13/2.33          | ~ (v1_relat_1 @ X0))),
% 2.13/2.33      inference('demod', [status(thm)], ['63', '66', '67', '68'])).
% 2.13/2.33  thf('70', plain,
% 2.13/2.33      ((((sk_A) != (sk_A))
% 2.13/2.33        | ~ (v1_relat_1 @ sk_D)
% 2.13/2.33        | ~ (v1_funct_1 @ sk_D)
% 2.13/2.33        | ((sk_C_1) = (sk_D))
% 2.13/2.33        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 2.13/2.33      inference('sup-', [status(thm)], ['38', '69'])).
% 2.13/2.33  thf('71', plain,
% 2.13/2.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf('72', plain,
% 2.13/2.33      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.13/2.33         ((v1_relat_1 @ X13)
% 2.13/2.33          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.13/2.33      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.13/2.33  thf('73', plain, ((v1_relat_1 @ sk_D)),
% 2.13/2.33      inference('sup-', [status(thm)], ['71', '72'])).
% 2.13/2.33  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf('75', plain,
% 2.13/2.33      ((((sk_A) != (sk_A))
% 2.13/2.33        | ((sk_C_1) = (sk_D))
% 2.13/2.33        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 2.13/2.33      inference('demod', [status(thm)], ['70', '73', '74'])).
% 2.13/2.33  thf('76', plain,
% 2.13/2.33      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 2.13/2.33      inference('simplify', [status(thm)], ['75'])).
% 2.13/2.33  thf(d10_xboole_0, axiom,
% 2.13/2.33    (![A:$i,B:$i]:
% 2.13/2.33     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.13/2.33  thf('77', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.13/2.33      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.13/2.33  thf('78', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.13/2.33      inference('simplify', [status(thm)], ['77'])).
% 2.13/2.33  thf(t3_subset, axiom,
% 2.13/2.33    (![A:$i,B:$i]:
% 2.13/2.33     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.13/2.33  thf('79', plain,
% 2.13/2.33      (![X5 : $i, X7 : $i]:
% 2.13/2.33         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 2.13/2.33      inference('cnf', [status(esa)], [t3_subset])).
% 2.13/2.33  thf('80', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.13/2.33      inference('sup-', [status(thm)], ['78', '79'])).
% 2.13/2.33  thf(t4_subset, axiom,
% 2.13/2.33    (![A:$i,B:$i,C:$i]:
% 2.13/2.33     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 2.13/2.33       ( m1_subset_1 @ A @ C ) ))).
% 2.13/2.33  thf('81', plain,
% 2.13/2.33      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.13/2.33         (~ (r2_hidden @ X8 @ X9)
% 2.13/2.33          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 2.13/2.33          | (m1_subset_1 @ X8 @ X10))),
% 2.13/2.33      inference('cnf', [status(esa)], [t4_subset])).
% 2.13/2.33  thf('82', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 2.13/2.33      inference('sup-', [status(thm)], ['80', '81'])).
% 2.13/2.33  thf('83', plain,
% 2.13/2.33      ((((sk_C_1) = (sk_D)) | (m1_subset_1 @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 2.13/2.33      inference('sup-', [status(thm)], ['76', '82'])).
% 2.13/2.33  thf('84', plain,
% 2.13/2.33      (![X34 : $i]:
% 2.13/2.33         (((k1_funct_1 @ sk_C_1 @ X34) = (k1_funct_1 @ sk_D @ X34))
% 2.13/2.33          | ~ (m1_subset_1 @ X34 @ sk_A))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf('85', plain,
% 2.13/2.33      ((((sk_C_1) = (sk_D))
% 2.13/2.33        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 2.13/2.33            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 2.13/2.33      inference('sup-', [status(thm)], ['83', '84'])).
% 2.13/2.33  thf('86', plain,
% 2.13/2.33      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 2.13/2.33         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 2.13/2.33      inference('condensation', [status(thm)], ['85'])).
% 2.13/2.33  thf('87', plain,
% 2.13/2.33      (![X11 : $i, X12 : $i]:
% 2.13/2.33         (~ (v1_relat_1 @ X11)
% 2.13/2.33          | ~ (v1_funct_1 @ X11)
% 2.13/2.33          | ((X12) = (X11))
% 2.13/2.33          | ((k1_funct_1 @ X12 @ (sk_C @ X11 @ X12))
% 2.13/2.33              != (k1_funct_1 @ X11 @ (sk_C @ X11 @ X12)))
% 2.13/2.33          | ((k1_relat_1 @ X12) != (k1_relat_1 @ X11))
% 2.13/2.33          | ~ (v1_funct_1 @ X12)
% 2.13/2.33          | ~ (v1_relat_1 @ X12))),
% 2.13/2.33      inference('cnf', [status(esa)], [t9_funct_1])).
% 2.13/2.33  thf('88', plain,
% 2.13/2.33      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 2.13/2.33          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 2.13/2.33        | ~ (v1_relat_1 @ sk_C_1)
% 2.13/2.33        | ~ (v1_funct_1 @ sk_C_1)
% 2.13/2.33        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 2.13/2.33        | ((sk_C_1) = (sk_D))
% 2.13/2.33        | ~ (v1_funct_1 @ sk_D)
% 2.13/2.33        | ~ (v1_relat_1 @ sk_D))),
% 2.13/2.33      inference('sup-', [status(thm)], ['86', '87'])).
% 2.13/2.33  thf('89', plain, ((v1_relat_1 @ sk_C_1)),
% 2.13/2.33      inference('sup-', [status(thm)], ['64', '65'])).
% 2.13/2.33  thf('90', plain, ((v1_funct_1 @ sk_C_1)),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf('91', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 2.13/2.33      inference('clc', [status(thm)], ['55', '60'])).
% 2.13/2.33  thf('92', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.13/2.33      inference('clc', [status(thm)], ['28', '37'])).
% 2.13/2.33  thf('93', plain, ((v1_funct_1 @ sk_D)),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf('94', plain, ((v1_relat_1 @ sk_D)),
% 2.13/2.33      inference('sup-', [status(thm)], ['71', '72'])).
% 2.13/2.33  thf('95', plain,
% 2.13/2.33      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 2.13/2.33          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 2.13/2.33        | ((sk_A) != (sk_A))
% 2.13/2.33        | ((sk_C_1) = (sk_D)))),
% 2.13/2.33      inference('demod', [status(thm)],
% 2.13/2.33                ['88', '89', '90', '91', '92', '93', '94'])).
% 2.13/2.33  thf('96', plain, (((sk_C_1) = (sk_D))),
% 2.13/2.33      inference('simplify', [status(thm)], ['95'])).
% 2.13/2.33  thf('97', plain,
% 2.13/2.33      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.13/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.33  thf('98', plain,
% 2.13/2.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.33         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 2.13/2.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 2.13/2.33      inference('condensation', [status(thm)], ['2'])).
% 2.13/2.33  thf('99', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 2.13/2.33      inference('sup-', [status(thm)], ['97', '98'])).
% 2.13/2.33  thf('100', plain, ($false),
% 2.13/2.33      inference('demod', [status(thm)], ['0', '96', '99'])).
% 2.13/2.33  
% 2.13/2.33  % SZS output end Refutation
% 2.13/2.33  
% 2.13/2.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
