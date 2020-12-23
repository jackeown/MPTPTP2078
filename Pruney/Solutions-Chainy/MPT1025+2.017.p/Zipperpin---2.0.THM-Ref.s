%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i5cUVo7vsE

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:45 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 226 expanded)
%              Number of leaves         :   44 (  87 expanded)
%              Depth                    :   17
%              Number of atoms          :  721 (3002 expanded)
%              Number of equality atoms :   36 ( 113 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_4_type,type,(
    sk_D_4: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(t116_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ~ ( ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ~ ( ( r2_hidden @ F @ C )
                      & ( E
                        = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_4 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( ( k7_relset_1 @ X50 @ X51 @ X49 @ X52 )
        = ( k9_relat_1 @ X49 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_4 @ X0 )
      = ( k9_relat_1 @ sk_D_4 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_4 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X21: $i,X22: $i] :
      ( ( X21
       != ( k9_relat_1 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X22 @ X18 @ X19 ) @ X22 @ X18 @ X19 )
      | ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X18: $i,X19: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( r2_hidden @ X22 @ ( k9_relat_1 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X22 @ X18 @ X19 ) @ X22 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4 ) @ sk_E_2 @ sk_C_1 @ sk_D_4 )
    | ~ ( v1_funct_1 @ sk_D_4 )
    | ~ ( v1_relat_1 @ sk_D_4 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( v1_relat_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_4 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4 ) @ sk_E_2 @ sk_C_1 @ sk_D_4 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ X15 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4 ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X61: $i] :
      ( ( sk_E_2
       != ( k1_funct_1 @ sk_D_4 @ X61 ) )
      | ~ ( r2_hidden @ X61 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X61 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4 ) @ sk_A )
    | ( sk_E_2
     != ( k1_funct_1 @ sk_D_4 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4 ) @ sk_E_2 @ sk_C_1 @ sk_D_4 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('18',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k1_funct_1 @ X12 @ X13 ) )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_4 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4 ) @ sk_A )
    | ( sk_E_2 != sk_E_2 ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4 ) @ sk_E_2 @ sk_C_1 @ sk_D_4 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k1_relat_1 @ X12 ) )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4 ) @ ( k1_relat_1 @ sk_D_4 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_D_4 @ sk_A @ sk_B_1 ),
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

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('26',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( v1_funct_2 @ X57 @ X55 @ X56 )
      | ( X55
        = ( k1_relset_1 @ X55 @ X56 @ X57 ) )
      | ~ ( zip_tseitin_2 @ X57 @ X56 @ X55 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('27',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_4 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_4 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k1_relset_1 @ X47 @ X48 @ X46 )
        = ( k1_relat_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_4 )
    = ( k1_relat_1 @ sk_D_4 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_4 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_4 ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_6,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( zip_tseitin_1 @ X58 @ X59 )
      | ( zip_tseitin_2 @ X60 @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('34',plain,
    ( ( zip_tseitin_2 @ sk_D_4 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X53: $i,X54: $i] :
      ( ( zip_tseitin_1 @ X53 @ X54 )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('36',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('39',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( v5_relat_1 @ X43 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('40',plain,(
    v5_relat_1 @ sk_D_4 @ sk_B_1 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4 ) @ ( k1_relat_1 @ sk_D_4 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('42',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k1_relat_1 @ X33 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X33 @ X32 ) @ X34 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v5_relat_1 @ X33 @ X34 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_4 )
      | ~ ( v5_relat_1 @ sk_D_4 @ X0 )
      | ~ ( v1_funct_1 @ sk_D_4 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_4 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D_4 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('45',plain,(
    v1_funct_1 @ sk_D_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_4 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_D_4 @ X0 )
      | ( r2_hidden @ sk_E_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    r2_hidden @ sk_E_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['40','47'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('49',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X38 @ X39 )
      | ~ ( r1_tarski @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('50',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['37','50'])).

thf('52',plain,(
    zip_tseitin_2 @ sk_D_4 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['34','51'])).

thf('53',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_4 ) ),
    inference(demod,[status(thm)],['31','52'])).

thf('54',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4 ) @ sk_A ),
    inference(demod,[status(thm)],['24','53'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('55',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('56',plain,(
    m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4 ) @ sk_A ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['21','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i5cUVo7vsE
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:48:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.79/2.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.79/2.05  % Solved by: fo/fo7.sh
% 1.79/2.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.79/2.05  % done 650 iterations in 1.589s
% 1.79/2.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.79/2.05  % SZS output start Refutation
% 1.79/2.05  thf(sk_D_4_type, type, sk_D_4: $i).
% 1.79/2.05  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.79/2.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.79/2.05  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.79/2.05  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.79/2.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.79/2.05  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.79/2.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.79/2.05  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.79/2.05  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.79/2.05  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.79/2.05  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.79/2.05  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.79/2.05  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.79/2.05  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 1.79/2.05  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.79/2.05  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.79/2.05  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.79/2.05  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.79/2.05  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.79/2.05  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 1.79/2.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.79/2.05  thf(sk_A_type, type, sk_A: $i).
% 1.79/2.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.79/2.05  thf(sk_E_2_type, type, sk_E_2: $i).
% 1.79/2.05  thf(t116_funct_2, conjecture,
% 1.79/2.05    (![A:$i,B:$i,C:$i,D:$i]:
% 1.79/2.05     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.79/2.05         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.79/2.05       ( ![E:$i]:
% 1.79/2.05         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.79/2.05              ( ![F:$i]:
% 1.79/2.05                ( ( m1_subset_1 @ F @ A ) =>
% 1.79/2.05                  ( ~( ( r2_hidden @ F @ C ) & 
% 1.79/2.05                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 1.79/2.05  thf(zf_stmt_0, negated_conjecture,
% 1.79/2.05    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.79/2.05        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.79/2.05            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.79/2.05          ( ![E:$i]:
% 1.79/2.05            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.79/2.05                 ( ![F:$i]:
% 1.79/2.05                   ( ( m1_subset_1 @ F @ A ) =>
% 1.79/2.05                     ( ~( ( r2_hidden @ F @ C ) & 
% 1.79/2.05                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 1.79/2.05    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 1.79/2.05  thf('0', plain,
% 1.79/2.05      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_4 @ sk_C_1))),
% 1.79/2.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.05  thf('1', plain,
% 1.79/2.05      ((m1_subset_1 @ sk_D_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.79/2.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.05  thf(redefinition_k7_relset_1, axiom,
% 1.79/2.05    (![A:$i,B:$i,C:$i,D:$i]:
% 1.79/2.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.79/2.05       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.79/2.05  thf('2', plain,
% 1.79/2.05      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 1.79/2.05         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 1.79/2.05          | ((k7_relset_1 @ X50 @ X51 @ X49 @ X52) = (k9_relat_1 @ X49 @ X52)))),
% 1.79/2.05      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.79/2.05  thf('3', plain,
% 1.79/2.05      (![X0 : $i]:
% 1.79/2.05         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_4 @ X0)
% 1.79/2.05           = (k9_relat_1 @ sk_D_4 @ X0))),
% 1.79/2.05      inference('sup-', [status(thm)], ['1', '2'])).
% 1.79/2.05  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_4 @ sk_C_1))),
% 1.79/2.05      inference('demod', [status(thm)], ['0', '3'])).
% 1.79/2.05  thf(d12_funct_1, axiom,
% 1.79/2.05    (![A:$i]:
% 1.79/2.05     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 1.79/2.05       ( ![B:$i,C:$i]:
% 1.79/2.05         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 1.79/2.05           ( ![D:$i]:
% 1.79/2.05             ( ( r2_hidden @ D @ C ) <=>
% 1.79/2.05               ( ?[E:$i]:
% 1.79/2.05                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 1.79/2.05                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 1.79/2.05  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.79/2.05  thf(zf_stmt_2, axiom,
% 1.79/2.05    (![E:$i,D:$i,B:$i,A:$i]:
% 1.79/2.05     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 1.79/2.05       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 1.79/2.05         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 1.79/2.05  thf(zf_stmt_3, axiom,
% 1.79/2.05    (![A:$i]:
% 1.79/2.05     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.79/2.05       ( ![B:$i,C:$i]:
% 1.79/2.05         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 1.79/2.05           ( ![D:$i]:
% 1.79/2.05             ( ( r2_hidden @ D @ C ) <=>
% 1.79/2.05               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 1.79/2.05  thf('5', plain,
% 1.79/2.05      (![X18 : $i, X19 : $i, X21 : $i, X22 : $i]:
% 1.79/2.05         (((X21) != (k9_relat_1 @ X19 @ X18))
% 1.79/2.05          | (zip_tseitin_0 @ (sk_E_1 @ X22 @ X18 @ X19) @ X22 @ X18 @ X19)
% 1.79/2.05          | ~ (r2_hidden @ X22 @ X21)
% 1.79/2.05          | ~ (v1_funct_1 @ X19)
% 1.79/2.05          | ~ (v1_relat_1 @ X19))),
% 1.79/2.05      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.79/2.05  thf('6', plain,
% 1.79/2.05      (![X18 : $i, X19 : $i, X22 : $i]:
% 1.79/2.05         (~ (v1_relat_1 @ X19)
% 1.79/2.05          | ~ (v1_funct_1 @ X19)
% 1.79/2.05          | ~ (r2_hidden @ X22 @ (k9_relat_1 @ X19 @ X18))
% 1.79/2.05          | (zip_tseitin_0 @ (sk_E_1 @ X22 @ X18 @ X19) @ X22 @ X18 @ X19))),
% 1.79/2.05      inference('simplify', [status(thm)], ['5'])).
% 1.79/2.05  thf('7', plain,
% 1.79/2.05      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4) @ sk_E_2 @ 
% 1.79/2.05         sk_C_1 @ sk_D_4)
% 1.79/2.05        | ~ (v1_funct_1 @ sk_D_4)
% 1.79/2.05        | ~ (v1_relat_1 @ sk_D_4))),
% 1.79/2.05      inference('sup-', [status(thm)], ['4', '6'])).
% 1.79/2.05  thf('8', plain, ((v1_funct_1 @ sk_D_4)),
% 1.79/2.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.05  thf('9', plain,
% 1.79/2.05      ((m1_subset_1 @ sk_D_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.79/2.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.05  thf(cc1_relset_1, axiom,
% 1.79/2.05    (![A:$i,B:$i,C:$i]:
% 1.79/2.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.79/2.05       ( v1_relat_1 @ C ) ))).
% 1.79/2.05  thf('10', plain,
% 1.79/2.05      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.79/2.05         ((v1_relat_1 @ X40)
% 1.79/2.05          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 1.79/2.05      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.79/2.05  thf('11', plain, ((v1_relat_1 @ sk_D_4)),
% 1.79/2.05      inference('sup-', [status(thm)], ['9', '10'])).
% 1.79/2.05  thf('12', plain,
% 1.79/2.05      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4) @ sk_E_2 @ 
% 1.79/2.05        sk_C_1 @ sk_D_4)),
% 1.79/2.05      inference('demod', [status(thm)], ['7', '8', '11'])).
% 1.79/2.05  thf('13', plain,
% 1.79/2.05      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.79/2.05         ((r2_hidden @ X13 @ X15) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 1.79/2.05      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.79/2.05  thf('14', plain,
% 1.79/2.05      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4) @ sk_C_1)),
% 1.79/2.05      inference('sup-', [status(thm)], ['12', '13'])).
% 1.79/2.05  thf('15', plain,
% 1.79/2.05      (![X61 : $i]:
% 1.79/2.05         (((sk_E_2) != (k1_funct_1 @ sk_D_4 @ X61))
% 1.79/2.05          | ~ (r2_hidden @ X61 @ sk_C_1)
% 1.79/2.05          | ~ (m1_subset_1 @ X61 @ sk_A))),
% 1.79/2.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.05  thf('16', plain,
% 1.79/2.05      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4) @ sk_A)
% 1.79/2.05        | ((sk_E_2)
% 1.79/2.05            != (k1_funct_1 @ sk_D_4 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4))))),
% 1.79/2.05      inference('sup-', [status(thm)], ['14', '15'])).
% 1.79/2.05  thf('17', plain,
% 1.79/2.05      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4) @ sk_E_2 @ 
% 1.79/2.05        sk_C_1 @ sk_D_4)),
% 1.79/2.05      inference('demod', [status(thm)], ['7', '8', '11'])).
% 1.79/2.05  thf('18', plain,
% 1.79/2.05      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.79/2.05         (((X14) = (k1_funct_1 @ X12 @ X13))
% 1.79/2.05          | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 1.79/2.05      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.79/2.05  thf('19', plain,
% 1.79/2.05      (((sk_E_2) = (k1_funct_1 @ sk_D_4 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4)))),
% 1.79/2.05      inference('sup-', [status(thm)], ['17', '18'])).
% 1.79/2.05  thf('20', plain,
% 1.79/2.05      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4) @ sk_A)
% 1.79/2.05        | ((sk_E_2) != (sk_E_2)))),
% 1.79/2.05      inference('demod', [status(thm)], ['16', '19'])).
% 1.79/2.05  thf('21', plain,
% 1.79/2.05      (~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4) @ sk_A)),
% 1.79/2.05      inference('simplify', [status(thm)], ['20'])).
% 1.79/2.05  thf('22', plain,
% 1.79/2.05      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4) @ sk_E_2 @ 
% 1.79/2.05        sk_C_1 @ sk_D_4)),
% 1.79/2.05      inference('demod', [status(thm)], ['7', '8', '11'])).
% 1.79/2.05  thf('23', plain,
% 1.79/2.05      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.79/2.05         ((r2_hidden @ X13 @ (k1_relat_1 @ X12))
% 1.79/2.05          | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 1.79/2.05      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.79/2.05  thf('24', plain,
% 1.79/2.05      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4) @ (k1_relat_1 @ sk_D_4))),
% 1.79/2.05      inference('sup-', [status(thm)], ['22', '23'])).
% 1.79/2.05  thf('25', plain, ((v1_funct_2 @ sk_D_4 @ sk_A @ sk_B_1)),
% 1.79/2.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.05  thf(d1_funct_2, axiom,
% 1.79/2.05    (![A:$i,B:$i,C:$i]:
% 1.79/2.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.79/2.05       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.79/2.05           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.79/2.05             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.79/2.05         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.79/2.05           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.79/2.05             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.79/2.05  thf(zf_stmt_4, axiom,
% 1.79/2.05    (![C:$i,B:$i,A:$i]:
% 1.79/2.05     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 1.79/2.05       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.79/2.05  thf('26', plain,
% 1.79/2.05      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.79/2.05         (~ (v1_funct_2 @ X57 @ X55 @ X56)
% 1.79/2.05          | ((X55) = (k1_relset_1 @ X55 @ X56 @ X57))
% 1.79/2.05          | ~ (zip_tseitin_2 @ X57 @ X56 @ X55))),
% 1.79/2.05      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.79/2.05  thf('27', plain,
% 1.79/2.05      ((~ (zip_tseitin_2 @ sk_D_4 @ sk_B_1 @ sk_A)
% 1.79/2.05        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_4)))),
% 1.79/2.05      inference('sup-', [status(thm)], ['25', '26'])).
% 1.79/2.05  thf('28', plain,
% 1.79/2.05      ((m1_subset_1 @ sk_D_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.79/2.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.05  thf(redefinition_k1_relset_1, axiom,
% 1.79/2.05    (![A:$i,B:$i,C:$i]:
% 1.79/2.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.79/2.05       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.79/2.05  thf('29', plain,
% 1.79/2.05      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.79/2.05         (((k1_relset_1 @ X47 @ X48 @ X46) = (k1_relat_1 @ X46))
% 1.79/2.05          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 1.79/2.05      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.79/2.05  thf('30', plain,
% 1.79/2.05      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_4) = (k1_relat_1 @ sk_D_4))),
% 1.79/2.05      inference('sup-', [status(thm)], ['28', '29'])).
% 1.79/2.05  thf('31', plain,
% 1.79/2.05      ((~ (zip_tseitin_2 @ sk_D_4 @ sk_B_1 @ sk_A)
% 1.79/2.05        | ((sk_A) = (k1_relat_1 @ sk_D_4)))),
% 1.79/2.05      inference('demod', [status(thm)], ['27', '30'])).
% 1.79/2.05  thf('32', plain,
% 1.79/2.05      ((m1_subset_1 @ sk_D_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.79/2.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.05  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 1.79/2.05  thf(zf_stmt_6, type, zip_tseitin_1 : $i > $i > $o).
% 1.79/2.05  thf(zf_stmt_7, axiom,
% 1.79/2.05    (![B:$i,A:$i]:
% 1.79/2.05     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.79/2.05       ( zip_tseitin_1 @ B @ A ) ))).
% 1.79/2.05  thf(zf_stmt_8, axiom,
% 1.79/2.05    (![A:$i,B:$i,C:$i]:
% 1.79/2.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.79/2.05       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 1.79/2.05         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.79/2.05           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.79/2.05             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.79/2.05  thf('33', plain,
% 1.79/2.05      (![X58 : $i, X59 : $i, X60 : $i]:
% 1.79/2.05         (~ (zip_tseitin_1 @ X58 @ X59)
% 1.79/2.05          | (zip_tseitin_2 @ X60 @ X58 @ X59)
% 1.79/2.05          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X58))))),
% 1.79/2.05      inference('cnf', [status(esa)], [zf_stmt_8])).
% 1.79/2.05  thf('34', plain,
% 1.79/2.05      (((zip_tseitin_2 @ sk_D_4 @ sk_B_1 @ sk_A)
% 1.79/2.05        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A))),
% 1.79/2.05      inference('sup-', [status(thm)], ['32', '33'])).
% 1.79/2.05  thf('35', plain,
% 1.79/2.05      (![X53 : $i, X54 : $i]:
% 1.79/2.05         ((zip_tseitin_1 @ X53 @ X54) | ((X53) = (k1_xboole_0)))),
% 1.79/2.05      inference('cnf', [status(esa)], [zf_stmt_7])).
% 1.79/2.05  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.79/2.05  thf('36', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.79/2.05      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.79/2.05  thf('37', plain,
% 1.79/2.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.79/2.05         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 1.79/2.05      inference('sup+', [status(thm)], ['35', '36'])).
% 1.79/2.05  thf('38', plain,
% 1.79/2.05      ((m1_subset_1 @ sk_D_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.79/2.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.05  thf(cc2_relset_1, axiom,
% 1.79/2.05    (![A:$i,B:$i,C:$i]:
% 1.79/2.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.79/2.05       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.79/2.05  thf('39', plain,
% 1.79/2.05      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.79/2.05         ((v5_relat_1 @ X43 @ X45)
% 1.79/2.05          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 1.79/2.05      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.79/2.05  thf('40', plain, ((v5_relat_1 @ sk_D_4 @ sk_B_1)),
% 1.79/2.05      inference('sup-', [status(thm)], ['38', '39'])).
% 1.79/2.05  thf('41', plain,
% 1.79/2.05      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4) @ (k1_relat_1 @ sk_D_4))),
% 1.79/2.05      inference('sup-', [status(thm)], ['22', '23'])).
% 1.79/2.05  thf(t172_funct_1, axiom,
% 1.79/2.05    (![A:$i,B:$i]:
% 1.79/2.05     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 1.79/2.05       ( ![C:$i]:
% 1.79/2.05         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 1.79/2.05           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 1.79/2.05  thf('42', plain,
% 1.79/2.05      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.79/2.05         (~ (r2_hidden @ X32 @ (k1_relat_1 @ X33))
% 1.79/2.05          | (r2_hidden @ (k1_funct_1 @ X33 @ X32) @ X34)
% 1.79/2.05          | ~ (v1_funct_1 @ X33)
% 1.79/2.05          | ~ (v5_relat_1 @ X33 @ X34)
% 1.79/2.05          | ~ (v1_relat_1 @ X33))),
% 1.79/2.05      inference('cnf', [status(esa)], [t172_funct_1])).
% 1.79/2.05  thf('43', plain,
% 1.79/2.05      (![X0 : $i]:
% 1.79/2.05         (~ (v1_relat_1 @ sk_D_4)
% 1.79/2.05          | ~ (v5_relat_1 @ sk_D_4 @ X0)
% 1.79/2.05          | ~ (v1_funct_1 @ sk_D_4)
% 1.79/2.05          | (r2_hidden @ 
% 1.79/2.05             (k1_funct_1 @ sk_D_4 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4)) @ X0))),
% 1.79/2.05      inference('sup-', [status(thm)], ['41', '42'])).
% 1.79/2.05  thf('44', plain, ((v1_relat_1 @ sk_D_4)),
% 1.79/2.05      inference('sup-', [status(thm)], ['9', '10'])).
% 1.79/2.05  thf('45', plain, ((v1_funct_1 @ sk_D_4)),
% 1.79/2.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.05  thf('46', plain,
% 1.79/2.05      (((sk_E_2) = (k1_funct_1 @ sk_D_4 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4)))),
% 1.79/2.05      inference('sup-', [status(thm)], ['17', '18'])).
% 1.79/2.05  thf('47', plain,
% 1.79/2.05      (![X0 : $i]: (~ (v5_relat_1 @ sk_D_4 @ X0) | (r2_hidden @ sk_E_2 @ X0))),
% 1.79/2.05      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 1.79/2.05  thf('48', plain, ((r2_hidden @ sk_E_2 @ sk_B_1)),
% 1.79/2.05      inference('sup-', [status(thm)], ['40', '47'])).
% 1.79/2.05  thf(t7_ordinal1, axiom,
% 1.79/2.05    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.79/2.05  thf('49', plain,
% 1.79/2.05      (![X38 : $i, X39 : $i]:
% 1.79/2.05         (~ (r2_hidden @ X38 @ X39) | ~ (r1_tarski @ X39 @ X38))),
% 1.79/2.05      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.79/2.05  thf('50', plain, (~ (r1_tarski @ sk_B_1 @ sk_E_2)),
% 1.79/2.05      inference('sup-', [status(thm)], ['48', '49'])).
% 1.79/2.05  thf('51', plain, (![X0 : $i]: (zip_tseitin_1 @ sk_B_1 @ X0)),
% 1.79/2.05      inference('sup-', [status(thm)], ['37', '50'])).
% 1.79/2.05  thf('52', plain, ((zip_tseitin_2 @ sk_D_4 @ sk_B_1 @ sk_A)),
% 1.79/2.05      inference('demod', [status(thm)], ['34', '51'])).
% 1.79/2.05  thf('53', plain, (((sk_A) = (k1_relat_1 @ sk_D_4))),
% 1.79/2.05      inference('demod', [status(thm)], ['31', '52'])).
% 1.79/2.05  thf('54', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4) @ sk_A)),
% 1.79/2.05      inference('demod', [status(thm)], ['24', '53'])).
% 1.79/2.05  thf(t1_subset, axiom,
% 1.79/2.05    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.79/2.05  thf('55', plain,
% 1.79/2.05      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 1.79/2.05      inference('cnf', [status(esa)], [t1_subset])).
% 1.79/2.05  thf('56', plain,
% 1.79/2.05      ((m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_4) @ sk_A)),
% 1.79/2.05      inference('sup-', [status(thm)], ['54', '55'])).
% 1.79/2.05  thf('57', plain, ($false), inference('demod', [status(thm)], ['21', '56'])).
% 1.79/2.05  
% 1.79/2.05  % SZS output end Refutation
% 1.79/2.05  
% 1.89/2.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
