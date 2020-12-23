%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z0UHy7jTiW

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:28 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 960 expanded)
%              Number of leaves         :   37 ( 282 expanded)
%              Depth                    :   22
%              Number of atoms          :  937 (12804 expanded)
%              Number of equality atoms :   85 ( 772 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(t17_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
          & ! [E: $i] :
              ~ ( ( r2_hidden @ E @ A )
                & ( ( k1_funct_1 @ D @ E )
                  = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
            & ! [E: $i] :
                ~ ( ( r2_hidden @ E @ A )
                  & ( ( k1_funct_1 @ D @ E )
                    = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_2 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C_2 @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( X15
       != ( k2_relat_1 @ X13 ) )
      | ( r2_hidden @ ( sk_D_2 @ X16 @ X13 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,(
    ! [X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k2_relat_1 @ X13 ) )
      | ( r2_hidden @ ( sk_D_2 @ X16 @ X13 ) @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_2 @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C_2 @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ sk_B ),
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

thf('14',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('22',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C_2 @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_2 @ sk_D_3 ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X44: $i] :
      ( ~ ( r2_hidden @ X44 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_3 @ X44 )
       != sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_C_2 @ sk_D_3 ) )
     != sk_C_2 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ sk_C_2 @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('32',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( X15
       != ( k2_relat_1 @ X13 ) )
      | ( X16
        = ( k1_funct_1 @ X13 @ ( sk_D_2 @ X16 @ X13 ) ) )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('33',plain,(
    ! [X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k2_relat_1 @ X13 ) )
      | ( X16
        = ( k1_funct_1 @ X13 @ ( sk_D_2 @ X16 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_C_2
      = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_C_2 @ sk_D_3 ) ) )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('37',plain,
    ( sk_C_2
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_C_2 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_2 != sk_C_2 ) ),
    inference(demod,[status(thm)],['30','37'])).

thf('39',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['19','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['38'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41 != k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('45',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_3 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_3 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['38'])).

thf('49',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_3 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    r2_hidden @ sk_C_2 @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('52',plain,
    ( ( r2_hidden @ sk_C_2 @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('53',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('54',plain,
    ( ( r2_hidden @ sk_C_2 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('55',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['55'])).

thf('58',plain,(
    r2_hidden @ sk_C_2 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('59',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X6 ) @ X8 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('60',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_C_2 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_3 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('62',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X6 ) @ X8 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ ( k1_tarski @ sk_C_2 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('68',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['72'])).

thf('74',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['75'])).

thf('77',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['54','76'])).

thf('78',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['54','76'])).

thf('79',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['40','77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('81',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['54','76'])).

thf('82',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('84',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('86',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('87',plain,(
    ! [X36: $i] :
      ( zip_tseitin_0 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['85','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['88'])).

thf('90',plain,(
    zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['84','89'])).

thf('91',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['79','90'])).

thf('92',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C_2 @ sk_D_3 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['75'])).

thf('94',plain,(
    $false ),
    inference('sup-',[status(thm)],['92','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z0UHy7jTiW
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:01:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.76/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.96  % Solved by: fo/fo7.sh
% 0.76/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.96  % done 506 iterations in 0.528s
% 0.76/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.96  % SZS output start Refutation
% 0.76/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.96  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.96  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.76/0.96  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.96  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.76/0.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.96  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.76/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.76/0.96  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.76/0.96  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.76/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.96  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.76/0.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.96  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.76/0.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.76/0.96  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.76/0.96  thf(t17_funct_2, conjecture,
% 0.76/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.96     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.76/0.96         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.96       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.76/0.96            ( ![E:$i]:
% 0.76/0.96              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 0.76/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.96    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.96        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.76/0.96            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.96          ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.76/0.96               ( ![E:$i]:
% 0.76/0.96                 ( ~( ( r2_hidden @ E @ A ) & 
% 0.76/0.96                      ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ) )),
% 0.76/0.96    inference('cnf.neg', [status(esa)], [t17_funct_2])).
% 0.76/0.96  thf('0', plain,
% 0.76/0.96      ((r2_hidden @ sk_C_2 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_3))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('1', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(redefinition_k2_relset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.76/0.96  thf('2', plain,
% 0.76/0.96      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.76/0.96         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.76/0.96          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.76/0.96  thf('3', plain,
% 0.76/0.96      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 0.76/0.96      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.96  thf('4', plain, ((r2_hidden @ sk_C_2 @ (k2_relat_1 @ sk_D_3))),
% 0.76/0.96      inference('demod', [status(thm)], ['0', '3'])).
% 0.76/0.96  thf(d5_funct_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.76/0.96           ( ![C:$i]:
% 0.76/0.96             ( ( r2_hidden @ C @ B ) <=>
% 0.76/0.96               ( ?[D:$i]:
% 0.76/0.96                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.76/0.96                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.76/0.96  thf('5', plain,
% 0.76/0.96      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.76/0.96         (((X15) != (k2_relat_1 @ X13))
% 0.76/0.96          | (r2_hidden @ (sk_D_2 @ X16 @ X13) @ (k1_relat_1 @ X13))
% 0.76/0.96          | ~ (r2_hidden @ X16 @ X15)
% 0.76/0.96          | ~ (v1_funct_1 @ X13)
% 0.76/0.96          | ~ (v1_relat_1 @ X13))),
% 0.76/0.96      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.76/0.96  thf('6', plain,
% 0.76/0.96      (![X13 : $i, X16 : $i]:
% 0.76/0.96         (~ (v1_relat_1 @ X13)
% 0.76/0.96          | ~ (v1_funct_1 @ X13)
% 0.76/0.96          | ~ (r2_hidden @ X16 @ (k2_relat_1 @ X13))
% 0.76/0.96          | (r2_hidden @ (sk_D_2 @ X16 @ X13) @ (k1_relat_1 @ X13)))),
% 0.76/0.96      inference('simplify', [status(thm)], ['5'])).
% 0.76/0.96  thf('7', plain,
% 0.76/0.96      (((r2_hidden @ (sk_D_2 @ sk_C_2 @ sk_D_3) @ (k1_relat_1 @ sk_D_3))
% 0.76/0.96        | ~ (v1_funct_1 @ sk_D_3)
% 0.76/0.96        | ~ (v1_relat_1 @ sk_D_3))),
% 0.76/0.96      inference('sup-', [status(thm)], ['4', '6'])).
% 0.76/0.96  thf('8', plain, ((v1_funct_1 @ sk_D_3)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('9', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(cc1_relset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( v1_relat_1 @ C ) ))).
% 0.76/0.96  thf('10', plain,
% 0.76/0.96      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.76/0.96         ((v1_relat_1 @ X23)
% 0.76/0.96          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.76/0.96      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.76/0.96  thf('11', plain, ((v1_relat_1 @ sk_D_3)),
% 0.76/0.96      inference('sup-', [status(thm)], ['9', '10'])).
% 0.76/0.96  thf('12', plain,
% 0.76/0.96      ((r2_hidden @ (sk_D_2 @ sk_C_2 @ sk_D_3) @ (k1_relat_1 @ sk_D_3))),
% 0.76/0.96      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.76/0.96  thf('13', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(d1_funct_2, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.96           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.76/0.96             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.76/0.96         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.96           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.76/0.96             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.76/0.96  thf(zf_stmt_1, axiom,
% 0.76/0.96    (![C:$i,B:$i,A:$i]:
% 0.76/0.96     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.76/0.96       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.76/0.96  thf('14', plain,
% 0.76/0.96      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.76/0.96         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.76/0.96          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 0.76/0.96          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.96  thf('15', plain,
% 0.76/0.96      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.76/0.96        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_3)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['13', '14'])).
% 0.76/0.96  thf('16', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(redefinition_k1_relset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.76/0.96  thf('17', plain,
% 0.76/0.96      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.76/0.96         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.76/0.96          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/0.96  thf('18', plain,
% 0.76/0.96      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_3) = (k1_relat_1 @ sk_D_3))),
% 0.76/0.96      inference('sup-', [status(thm)], ['16', '17'])).
% 0.76/0.96  thf('19', plain,
% 0.76/0.96      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.76/0.96        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.76/0.96      inference('demod', [status(thm)], ['15', '18'])).
% 0.76/0.96  thf(zf_stmt_2, axiom,
% 0.76/0.96    (![B:$i,A:$i]:
% 0.76/0.96     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.96       ( zip_tseitin_0 @ B @ A ) ))).
% 0.76/0.96  thf('20', plain,
% 0.76/0.96      (![X36 : $i, X37 : $i]:
% 0.76/0.96         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/0.96  thf('21', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.76/0.96  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.76/0.96  thf(zf_stmt_5, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.76/0.96         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.96           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.76/0.96             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.76/0.96  thf('22', plain,
% 0.76/0.96      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.76/0.96         (~ (zip_tseitin_0 @ X41 @ X42)
% 0.76/0.96          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 0.76/0.96          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.96  thf('23', plain,
% 0.76/0.96      (((zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.76/0.96        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.96  thf('24', plain,
% 0.76/0.96      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['20', '23'])).
% 0.76/0.96  thf('25', plain,
% 0.76/0.96      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.76/0.96        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.76/0.96      inference('demod', [status(thm)], ['15', '18'])).
% 0.76/0.96  thf('26', plain,
% 0.76/0.96      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['24', '25'])).
% 0.76/0.96  thf('27', plain,
% 0.76/0.96      ((r2_hidden @ (sk_D_2 @ sk_C_2 @ sk_D_3) @ (k1_relat_1 @ sk_D_3))),
% 0.76/0.96      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.76/0.96  thf('28', plain,
% 0.76/0.96      (((r2_hidden @ (sk_D_2 @ sk_C_2 @ sk_D_3) @ sk_A)
% 0.76/0.96        | ((sk_B) = (k1_xboole_0)))),
% 0.76/0.96      inference('sup+', [status(thm)], ['26', '27'])).
% 0.76/0.96  thf('29', plain,
% 0.76/0.96      (![X44 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X44 @ sk_A)
% 0.76/0.96          | ((k1_funct_1 @ sk_D_3 @ X44) != (sk_C_2)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('30', plain,
% 0.76/0.96      ((((sk_B) = (k1_xboole_0))
% 0.76/0.96        | ((k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_C_2 @ sk_D_3)) != (sk_C_2)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['28', '29'])).
% 0.76/0.96  thf('31', plain, ((r2_hidden @ sk_C_2 @ (k2_relat_1 @ sk_D_3))),
% 0.76/0.96      inference('demod', [status(thm)], ['0', '3'])).
% 0.76/0.96  thf('32', plain,
% 0.76/0.96      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.76/0.96         (((X15) != (k2_relat_1 @ X13))
% 0.76/0.96          | ((X16) = (k1_funct_1 @ X13 @ (sk_D_2 @ X16 @ X13)))
% 0.76/0.96          | ~ (r2_hidden @ X16 @ X15)
% 0.76/0.96          | ~ (v1_funct_1 @ X13)
% 0.76/0.96          | ~ (v1_relat_1 @ X13))),
% 0.76/0.96      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.76/0.96  thf('33', plain,
% 0.76/0.96      (![X13 : $i, X16 : $i]:
% 0.76/0.96         (~ (v1_relat_1 @ X13)
% 0.76/0.96          | ~ (v1_funct_1 @ X13)
% 0.76/0.96          | ~ (r2_hidden @ X16 @ (k2_relat_1 @ X13))
% 0.76/0.96          | ((X16) = (k1_funct_1 @ X13 @ (sk_D_2 @ X16 @ X13))))),
% 0.76/0.96      inference('simplify', [status(thm)], ['32'])).
% 0.76/0.96  thf('34', plain,
% 0.76/0.96      ((((sk_C_2) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_C_2 @ sk_D_3)))
% 0.76/0.96        | ~ (v1_funct_1 @ sk_D_3)
% 0.76/0.96        | ~ (v1_relat_1 @ sk_D_3))),
% 0.76/0.96      inference('sup-', [status(thm)], ['31', '33'])).
% 0.76/0.96  thf('35', plain, ((v1_funct_1 @ sk_D_3)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('36', plain, ((v1_relat_1 @ sk_D_3)),
% 0.76/0.96      inference('sup-', [status(thm)], ['9', '10'])).
% 0.76/0.96  thf('37', plain,
% 0.76/0.96      (((sk_C_2) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_C_2 @ sk_D_3)))),
% 0.76/0.96      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.76/0.96  thf('38', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C_2) != (sk_C_2)))),
% 0.76/0.96      inference('demod', [status(thm)], ['30', '37'])).
% 0.76/0.96  thf('39', plain, (((sk_B) = (k1_xboole_0))),
% 0.76/0.96      inference('simplify', [status(thm)], ['38'])).
% 0.76/0.96  thf('40', plain,
% 0.76/0.96      ((~ (zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ sk_A)
% 0.76/0.96        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.76/0.96      inference('demod', [status(thm)], ['19', '39'])).
% 0.76/0.96  thf('41', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('42', plain, (((sk_B) = (k1_xboole_0))),
% 0.76/0.96      inference('simplify', [status(thm)], ['38'])).
% 0.76/0.96  thf('43', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D_3 @ 
% 0.76/0.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.76/0.96      inference('demod', [status(thm)], ['41', '42'])).
% 0.76/0.96  thf('44', plain,
% 0.76/0.96      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.76/0.96         (((X41) != (k1_xboole_0))
% 0.76/0.96          | ((X42) = (k1_xboole_0))
% 0.76/0.96          | ((X43) = (k1_xboole_0))
% 0.76/0.96          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 0.76/0.96          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.96  thf('45', plain,
% 0.76/0.96      (![X42 : $i, X43 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X43 @ 
% 0.76/0.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ k1_xboole_0)))
% 0.76/0.96          | ~ (v1_funct_2 @ X43 @ X42 @ k1_xboole_0)
% 0.76/0.96          | ((X43) = (k1_xboole_0))
% 0.76/0.96          | ((X42) = (k1_xboole_0)))),
% 0.76/0.96      inference('simplify', [status(thm)], ['44'])).
% 0.76/0.96  thf('46', plain,
% 0.76/0.96      ((((sk_A) = (k1_xboole_0))
% 0.76/0.96        | ((sk_D_3) = (k1_xboole_0))
% 0.76/0.96        | ~ (v1_funct_2 @ sk_D_3 @ sk_A @ k1_xboole_0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['43', '45'])).
% 0.76/0.96  thf('47', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('48', plain, (((sk_B) = (k1_xboole_0))),
% 0.76/0.96      inference('simplify', [status(thm)], ['38'])).
% 0.76/0.96  thf('49', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ k1_xboole_0)),
% 0.76/0.96      inference('demod', [status(thm)], ['47', '48'])).
% 0.76/0.96  thf('50', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_3) = (k1_xboole_0)))),
% 0.76/0.96      inference('demod', [status(thm)], ['46', '49'])).
% 0.76/0.96  thf('51', plain, ((r2_hidden @ sk_C_2 @ (k2_relat_1 @ sk_D_3))),
% 0.76/0.96      inference('demod', [status(thm)], ['0', '3'])).
% 0.76/0.96  thf('52', plain,
% 0.76/0.96      (((r2_hidden @ sk_C_2 @ (k2_relat_1 @ k1_xboole_0))
% 0.76/0.96        | ((sk_A) = (k1_xboole_0)))),
% 0.76/0.96      inference('sup+', [status(thm)], ['50', '51'])).
% 0.76/0.96  thf(t60_relat_1, axiom,
% 0.76/0.96    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.76/0.96     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.76/0.96  thf('53', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.96      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.76/0.96  thf('54', plain,
% 0.76/0.96      (((r2_hidden @ sk_C_2 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.76/0.96      inference('demod', [status(thm)], ['52', '53'])).
% 0.76/0.96  thf(d5_xboole_0, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.76/0.96       ( ![D:$i]:
% 0.76/0.96         ( ( r2_hidden @ D @ C ) <=>
% 0.76/0.96           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.76/0.96  thf('55', plain,
% 0.76/0.96      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.76/0.96         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.76/0.96          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.76/0.96          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.76/0.96      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/0.96  thf('56', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.76/0.96          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.76/0.96      inference('eq_fact', [status(thm)], ['55'])).
% 0.76/0.96  thf('57', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.76/0.96          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.76/0.96      inference('eq_fact', [status(thm)], ['55'])).
% 0.76/0.96  thf('58', plain,
% 0.76/0.96      ((r2_hidden @ sk_C_2 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_3))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(l35_zfmisc_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.76/0.96       ( r2_hidden @ A @ B ) ))).
% 0.76/0.96  thf('59', plain,
% 0.76/0.96      (![X6 : $i, X8 : $i]:
% 0.76/0.96         (((k4_xboole_0 @ (k1_tarski @ X6) @ X8) = (k1_xboole_0))
% 0.76/0.96          | ~ (r2_hidden @ X6 @ X8))),
% 0.76/0.96      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.76/0.96  thf('60', plain,
% 0.76/0.96      (((k4_xboole_0 @ (k1_tarski @ sk_C_2) @ 
% 0.76/0.96         (k2_relset_1 @ sk_A @ sk_B @ sk_D_3)) = (k1_xboole_0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['58', '59'])).
% 0.76/0.96  thf('61', plain,
% 0.76/0.96      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X4 @ X3)
% 0.76/0.96          | (r2_hidden @ X4 @ X1)
% 0.76/0.96          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.76/0.96      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/0.96  thf('62', plain,
% 0.76/0.96      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.76/0.96         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.76/0.96      inference('simplify', [status(thm)], ['61'])).
% 0.76/0.96  thf('63', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.76/0.96          | (r2_hidden @ X0 @ (k1_tarski @ sk_C_2)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['60', '62'])).
% 0.76/0.96  thf('64', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.76/0.96          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.76/0.96             (k1_tarski @ sk_C_2)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['57', '63'])).
% 0.76/0.96  thf('65', plain,
% 0.76/0.96      (![X6 : $i, X8 : $i]:
% 0.76/0.96         (((k4_xboole_0 @ (k1_tarski @ X6) @ X8) = (k1_xboole_0))
% 0.76/0.96          | ~ (r2_hidden @ X6 @ X8))),
% 0.76/0.96      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.76/0.96  thf('66', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.76/0.96          | ((k4_xboole_0 @ 
% 0.76/0.96              (k1_tarski @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.76/0.96              (k1_tarski @ sk_C_2)) = (k1_xboole_0)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['64', '65'])).
% 0.76/0.96  thf('67', plain,
% 0.76/0.96      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X4 @ X3)
% 0.76/0.96          | ~ (r2_hidden @ X4 @ X2)
% 0.76/0.96          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.76/0.96      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/0.96  thf('68', plain,
% 0.76/0.96      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X4 @ X2)
% 0.76/0.96          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.76/0.96      inference('simplify', [status(thm)], ['67'])).
% 0.76/0.96  thf('69', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.76/0.96          | ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.76/0.96          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C_2)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['66', '68'])).
% 0.76/0.96  thf('70', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.76/0.96          | (r2_hidden @ X0 @ (k1_tarski @ sk_C_2)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['60', '62'])).
% 0.76/0.96  thf('71', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.76/0.96          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.76/0.96      inference('clc', [status(thm)], ['69', '70'])).
% 0.76/0.96  thf('72', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.76/0.96          | ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['56', '71'])).
% 0.76/0.96  thf('73', plain,
% 0.76/0.96      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.76/0.96      inference('condensation', [status(thm)], ['72'])).
% 0.76/0.96  thf('74', plain,
% 0.76/0.96      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X4 @ X2)
% 0.76/0.96          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.76/0.96      inference('simplify', [status(thm)], ['67'])).
% 0.76/0.96  thf('75', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['73', '74'])).
% 0.76/0.96  thf('76', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.76/0.96      inference('condensation', [status(thm)], ['75'])).
% 0.76/0.96  thf('77', plain, (((sk_A) = (k1_xboole_0))),
% 0.76/0.96      inference('clc', [status(thm)], ['54', '76'])).
% 0.76/0.96  thf('78', plain, (((sk_A) = (k1_xboole_0))),
% 0.76/0.96      inference('clc', [status(thm)], ['54', '76'])).
% 0.76/0.96  thf('79', plain,
% 0.76/0.96      ((~ (zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ k1_xboole_0)
% 0.76/0.96        | ((k1_xboole_0) = (k1_relat_1 @ sk_D_3)))),
% 0.76/0.96      inference('demod', [status(thm)], ['40', '77', '78'])).
% 0.76/0.96  thf('80', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D_3 @ 
% 0.76/0.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.76/0.96      inference('demod', [status(thm)], ['41', '42'])).
% 0.76/0.96  thf('81', plain, (((sk_A) = (k1_xboole_0))),
% 0.76/0.96      inference('clc', [status(thm)], ['54', '76'])).
% 0.76/0.96  thf('82', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D_3 @ 
% 0.76/0.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.76/0.96      inference('demod', [status(thm)], ['80', '81'])).
% 0.76/0.96  thf('83', plain,
% 0.76/0.96      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.76/0.96         (~ (zip_tseitin_0 @ X41 @ X42)
% 0.76/0.96          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 0.76/0.96          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.96  thf('84', plain,
% 0.76/0.96      (((zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ k1_xboole_0)
% 0.76/0.96        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['82', '83'])).
% 0.76/0.96  thf('85', plain,
% 0.76/0.96      (![X36 : $i, X37 : $i]:
% 0.76/0.96         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/0.96  thf('86', plain,
% 0.76/0.96      (![X36 : $i, X37 : $i]:
% 0.76/0.96         ((zip_tseitin_0 @ X36 @ X37) | ((X37) != (k1_xboole_0)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/0.96  thf('87', plain, (![X36 : $i]: (zip_tseitin_0 @ X36 @ k1_xboole_0)),
% 0.76/0.96      inference('simplify', [status(thm)], ['86'])).
% 0.76/0.96  thf('88', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.96         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.76/0.96      inference('sup+', [status(thm)], ['85', '87'])).
% 0.76/0.96  thf('89', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.76/0.96      inference('eq_fact', [status(thm)], ['88'])).
% 0.76/0.96  thf('90', plain, ((zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ k1_xboole_0)),
% 0.76/0.96      inference('demod', [status(thm)], ['84', '89'])).
% 0.76/0.96  thf('91', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_3))),
% 0.76/0.96      inference('demod', [status(thm)], ['79', '90'])).
% 0.76/0.96  thf('92', plain, ((r2_hidden @ (sk_D_2 @ sk_C_2 @ sk_D_3) @ k1_xboole_0)),
% 0.76/0.96      inference('demod', [status(thm)], ['12', '91'])).
% 0.76/0.96  thf('93', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.76/0.96      inference('condensation', [status(thm)], ['75'])).
% 0.76/0.96  thf('94', plain, ($false), inference('sup-', [status(thm)], ['92', '93'])).
% 0.76/0.96  
% 0.76/0.96  % SZS output end Refutation
% 0.76/0.96  
% 0.76/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
