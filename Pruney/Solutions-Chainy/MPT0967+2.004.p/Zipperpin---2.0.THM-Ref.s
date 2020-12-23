%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4vJRGjDRk6

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:11 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  192 (1686 expanded)
%              Number of leaves         :   52 ( 486 expanded)
%              Depth                    :   25
%              Number of atoms          : 1418 (21637 expanded)
%              Number of equality atoms :  111 (1365 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t9_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ B @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_funct_2])).

thf('0',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_D @ sk_B_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v5_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('8',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B_1 ),
    inference(demod,[status(thm)],['5','8'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['0','11'])).

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

thf('13',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ( X45
        = ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('27',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['0','11'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ X35 )
      | ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('36',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('37',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45
       != ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['40'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('46',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['40'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['40'])).

thf('49',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['44','47','48'])).

thf('50',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['41','49'])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ( sk_A
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['39','50'])).

thf('52',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_A
     != ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','51'])).

thf('53',plain,
    ( ( sk_A != sk_A )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','52'])).

thf('54',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('60',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X27 ) ) )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('61',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('62',plain,(
    ! [X14: $i] :
      ( ( r1_xboole_0 @ X14 @ X14 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('63',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('64',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('65',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('66',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','70'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('72',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('73',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['0','11'])).

thf('75',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('77',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('78',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ X35 )
      | ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) )
        | ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('83',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C_1 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','69'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('85',plain,(
    ! [X18: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('86',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','88'])).

thf('90',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45
       != ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('91',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_C_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_C_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('94',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('95',plain,
    ( ( ( zip_tseitin_1 @ k1_xboole_0 @ sk_C_1 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_C_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X44 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('97',plain,(
    ! [X43: $i] :
      ( zip_tseitin_0 @ X43 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( zip_tseitin_1 @ k1_xboole_0 @ sk_C_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','97'])).

thf('99',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','98'])).

thf('100',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('101',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('102',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['40'])).

thf('103',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('107',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('108',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('109',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['40'])).

thf('110',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['40'])).

thf('114',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('115',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['44','105','112','113','114'])).

thf('116',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['56','115'])).

thf('117',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['54','116'])).

thf('118',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
            & ( v1_funct_2 @ D @ A @ C )
            & ( v1_funct_1 @ D ) )
          | ( ( A != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_8,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_9,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ A )
     => ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_10,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( zip_tseitin_3 @ B @ A )
          | ( zip_tseitin_2 @ D @ C @ A ) ) ) ) )).

thf('120',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( zip_tseitin_3 @ X56 @ X57 )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_funct_2 @ X58 @ X57 @ X56 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X56 ) ) )
      | ( zip_tseitin_2 @ X58 @ X59 @ X57 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X57 @ X56 @ X58 ) @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ X0 )
      | ( zip_tseitin_2 @ sk_D @ X0 @ sk_A )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( zip_tseitin_3 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('123',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('124',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ( zip_tseitin_2 @ sk_D @ X0 @ sk_A )
      | ( zip_tseitin_3 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','124','125','126'])).

thf('128',plain,
    ( ( zip_tseitin_3 @ sk_B_1 @ sk_A )
    | ( zip_tseitin_2 @ sk_D @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','127'])).

thf('129',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( v1_funct_2 @ X51 @ X53 @ X52 )
      | ~ ( zip_tseitin_2 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('130',plain,
    ( ( zip_tseitin_3 @ sk_B_1 @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['41','49'])).

thf('132',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['54','116'])).

thf('133',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    zip_tseitin_3 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['130','133'])).

thf('135',plain,(
    ! [X54: $i,X55: $i] :
      ( ( X54 = k1_xboole_0 )
      | ~ ( zip_tseitin_3 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('136',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['56','115'])).

thf('138',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['136','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4vJRGjDRk6
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.74/1.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.74/1.98  % Solved by: fo/fo7.sh
% 1.74/1.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.74/1.98  % done 2155 iterations in 1.516s
% 1.74/1.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.74/1.98  % SZS output start Refutation
% 1.74/1.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.74/1.98  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 1.74/1.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.74/1.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.74/1.98  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.74/1.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.74/1.98  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 1.74/1.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.74/1.98  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.74/1.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.74/1.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.74/1.98  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.74/1.98  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.74/1.98  thf(sk_D_type, type, sk_D: $i).
% 1.74/1.98  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.74/1.98  thf(sk_A_type, type, sk_A: $i).
% 1.74/1.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.74/1.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.74/1.98  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.74/1.98  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.74/1.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.74/1.98  thf(sk_B_type, type, sk_B: $i > $i).
% 1.74/1.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.74/1.98  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.74/1.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.74/1.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.74/1.98  thf(t9_funct_2, conjecture,
% 1.74/1.98    (![A:$i,B:$i,C:$i,D:$i]:
% 1.74/1.98     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.74/1.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.74/1.98       ( ( r1_tarski @ B @ C ) =>
% 1.74/1.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.74/1.98           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.74/1.98             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 1.74/1.98  thf(zf_stmt_0, negated_conjecture,
% 1.74/1.98    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.74/1.98        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.74/1.98            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.74/1.98          ( ( r1_tarski @ B @ C ) =>
% 1.74/1.98            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.74/1.98              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.74/1.98                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 1.74/1.98    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 1.74/1.98  thf('0', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('1', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(cc2_relset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.98       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.74/1.98  thf('2', plain,
% 1.74/1.98      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.74/1.98         ((v5_relat_1 @ X22 @ X24)
% 1.74/1.98          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.74/1.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.74/1.98  thf('3', plain, ((v5_relat_1 @ sk_D @ sk_B_1)),
% 1.74/1.98      inference('sup-', [status(thm)], ['1', '2'])).
% 1.74/1.98  thf(d19_relat_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( v1_relat_1 @ B ) =>
% 1.74/1.98       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.74/1.98  thf('4', plain,
% 1.74/1.98      (![X16 : $i, X17 : $i]:
% 1.74/1.98         (~ (v5_relat_1 @ X16 @ X17)
% 1.74/1.98          | (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 1.74/1.98          | ~ (v1_relat_1 @ X16))),
% 1.74/1.98      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.74/1.98  thf('5', plain,
% 1.74/1.98      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B_1))),
% 1.74/1.98      inference('sup-', [status(thm)], ['3', '4'])).
% 1.74/1.98  thf('6', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(cc1_relset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.98       ( v1_relat_1 @ C ) ))).
% 1.74/1.98  thf('7', plain,
% 1.74/1.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.74/1.98         ((v1_relat_1 @ X19)
% 1.74/1.98          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.74/1.98      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.74/1.98  thf('8', plain, ((v1_relat_1 @ sk_D)),
% 1.74/1.98      inference('sup-', [status(thm)], ['6', '7'])).
% 1.74/1.98  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B_1)),
% 1.74/1.98      inference('demod', [status(thm)], ['5', '8'])).
% 1.74/1.98  thf(t1_xboole_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.74/1.98       ( r1_tarski @ A @ C ) ))).
% 1.74/1.98  thf('10', plain,
% 1.74/1.98      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.74/1.98         (~ (r1_tarski @ X11 @ X12)
% 1.74/1.98          | ~ (r1_tarski @ X12 @ X13)
% 1.74/1.98          | (r1_tarski @ X11 @ X13))),
% 1.74/1.98      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.74/1.98  thf('11', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0) | ~ (r1_tarski @ sk_B_1 @ X0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['9', '10'])).
% 1.74/1.98  thf('12', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 1.74/1.98      inference('sup-', [status(thm)], ['0', '11'])).
% 1.74/1.98  thf(d1_funct_2, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.98       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.74/1.98           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.74/1.98             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.74/1.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.74/1.98           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.74/1.98             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.74/1.98  thf(zf_stmt_1, axiom,
% 1.74/1.98    (![B:$i,A:$i]:
% 1.74/1.98     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.74/1.98       ( zip_tseitin_0 @ B @ A ) ))).
% 1.74/1.98  thf('13', plain,
% 1.74/1.98      (![X43 : $i, X44 : $i]:
% 1.74/1.98         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.74/1.98  thf('14', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.74/1.98  thf(zf_stmt_3, axiom,
% 1.74/1.98    (![C:$i,B:$i,A:$i]:
% 1.74/1.98     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.74/1.98       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.74/1.98  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.74/1.98  thf(zf_stmt_5, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.98       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.74/1.98         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.74/1.98           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.74/1.98             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.74/1.98  thf('15', plain,
% 1.74/1.98      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.74/1.98         (~ (zip_tseitin_0 @ X48 @ X49)
% 1.74/1.98          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 1.74/1.98          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.74/1.98  thf('16', plain,
% 1.74/1.98      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.74/1.98        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.74/1.98      inference('sup-', [status(thm)], ['14', '15'])).
% 1.74/1.98  thf('17', plain,
% 1.74/1.98      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 1.74/1.98      inference('sup-', [status(thm)], ['13', '16'])).
% 1.74/1.98  thf('18', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('19', plain,
% 1.74/1.98      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.74/1.98         (~ (v1_funct_2 @ X47 @ X45 @ X46)
% 1.74/1.98          | ((X45) = (k1_relset_1 @ X45 @ X46 @ X47))
% 1.74/1.98          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.74/1.98  thf('20', plain,
% 1.74/1.98      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.74/1.98        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['18', '19'])).
% 1.74/1.98  thf('21', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(redefinition_k1_relset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.98       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.74/1.98  thf('22', plain,
% 1.74/1.98      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.74/1.98         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 1.74/1.98          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.74/1.98  thf('23', plain,
% 1.74/1.98      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.74/1.98      inference('sup-', [status(thm)], ['21', '22'])).
% 1.74/1.98  thf('24', plain,
% 1.74/1.98      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.74/1.98        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.74/1.98      inference('demod', [status(thm)], ['20', '23'])).
% 1.74/1.98  thf('25', plain,
% 1.74/1.98      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['17', '24'])).
% 1.74/1.98  thf('26', plain,
% 1.74/1.98      (![X43 : $i, X44 : $i]:
% 1.74/1.98         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.74/1.98  thf('27', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 1.74/1.98      inference('sup-', [status(thm)], ['0', '11'])).
% 1.74/1.98  thf('28', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(t14_relset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i,D:$i]:
% 1.74/1.98     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.74/1.98       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 1.74/1.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 1.74/1.98  thf('29', plain,
% 1.74/1.98      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.74/1.98         (~ (r1_tarski @ (k2_relat_1 @ X34) @ X35)
% 1.74/1.98          | (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 1.74/1.98          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 1.74/1.98      inference('cnf', [status(esa)], [t14_relset_1])).
% 1.74/1.98  thf('30', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.74/1.98          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['28', '29'])).
% 1.74/1.98  thf('31', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['27', '30'])).
% 1.74/1.98  thf('32', plain,
% 1.74/1.98      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.74/1.98         (~ (zip_tseitin_0 @ X48 @ X49)
% 1.74/1.98          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 1.74/1.98          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.74/1.98  thf('33', plain,
% 1.74/1.98      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 1.74/1.98        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_A))),
% 1.74/1.98      inference('sup-', [status(thm)], ['31', '32'])).
% 1.74/1.98  thf('34', plain,
% 1.74/1.98      ((((sk_C_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A))),
% 1.74/1.98      inference('sup-', [status(thm)], ['26', '33'])).
% 1.74/1.98  thf('35', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['27', '30'])).
% 1.74/1.98  thf('36', plain,
% 1.74/1.98      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.74/1.98         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 1.74/1.98          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.74/1.98  thf('37', plain,
% 1.74/1.98      (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.74/1.98      inference('sup-', [status(thm)], ['35', '36'])).
% 1.74/1.98  thf('38', plain,
% 1.74/1.98      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.74/1.98         (((X45) != (k1_relset_1 @ X45 @ X46 @ X47))
% 1.74/1.98          | (v1_funct_2 @ X47 @ X45 @ X46)
% 1.74/1.98          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.74/1.98  thf('39', plain,
% 1.74/1.98      ((((sk_A) != (k1_relat_1 @ sk_D))
% 1.74/1.98        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 1.74/1.98        | (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 1.74/1.98      inference('sup-', [status(thm)], ['37', '38'])).
% 1.74/1.98  thf('40', plain,
% 1.74/1.98      ((~ (v1_funct_1 @ sk_D)
% 1.74/1.98        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 1.74/1.98        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('41', plain,
% 1.74/1.98      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 1.74/1.98         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.74/1.98      inference('split', [status(esa)], ['40'])).
% 1.74/1.98  thf('42', plain, ((v1_funct_1 @ sk_D)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('43', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 1.74/1.98      inference('split', [status(esa)], ['40'])).
% 1.74/1.98  thf('44', plain, (((v1_funct_1 @ sk_D))),
% 1.74/1.98      inference('sup-', [status(thm)], ['42', '43'])).
% 1.74/1.98  thf('45', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['27', '30'])).
% 1.74/1.98  thf('46', plain,
% 1.74/1.98      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 1.74/1.98         <= (~
% 1.74/1.98             ((m1_subset_1 @ sk_D @ 
% 1.74/1.98               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 1.74/1.98      inference('split', [status(esa)], ['40'])).
% 1.74/1.98  thf('47', plain,
% 1.74/1.98      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['45', '46'])).
% 1.74/1.98  thf('48', plain,
% 1.74/1.98      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | 
% 1.74/1.98       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 1.74/1.98       ~ ((v1_funct_1 @ sk_D))),
% 1.74/1.98      inference('split', [status(esa)], ['40'])).
% 1.74/1.98  thf('49', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 1.74/1.98      inference('sat_resolution*', [status(thm)], ['44', '47', '48'])).
% 1.74/1.98  thf('50', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 1.74/1.98      inference('simpl_trail', [status(thm)], ['41', '49'])).
% 1.74/1.98  thf('51', plain,
% 1.74/1.98      ((~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 1.74/1.98        | ((sk_A) != (k1_relat_1 @ sk_D)))),
% 1.74/1.98      inference('clc', [status(thm)], ['39', '50'])).
% 1.74/1.98  thf('52', plain,
% 1.74/1.98      ((((sk_C_1) = (k1_xboole_0)) | ((sk_A) != (k1_relat_1 @ sk_D)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['34', '51'])).
% 1.74/1.98  thf('53', plain,
% 1.74/1.98      ((((sk_A) != (sk_A))
% 1.74/1.98        | ((sk_B_1) = (k1_xboole_0))
% 1.74/1.98        | ((sk_C_1) = (k1_xboole_0)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['25', '52'])).
% 1.74/1.98  thf('54', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 1.74/1.98      inference('simplify', [status(thm)], ['53'])).
% 1.74/1.98  thf('55', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('56', plain,
% 1.74/1.98      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.74/1.98      inference('split', [status(esa)], ['55'])).
% 1.74/1.98  thf('57', plain,
% 1.74/1.98      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('split', [status(esa)], ['55'])).
% 1.74/1.98  thf('58', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('59', plain,
% 1.74/1.98      (((m1_subset_1 @ sk_D @ 
% 1.74/1.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.74/1.98         <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup+', [status(thm)], ['57', '58'])).
% 1.74/1.98  thf(cc3_relset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( v1_xboole_0 @ A ) =>
% 1.74/1.98       ( ![C:$i]:
% 1.74/1.98         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.98           ( v1_xboole_0 @ C ) ) ) ))).
% 1.74/1.98  thf('60', plain,
% 1.74/1.98      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.74/1.98         (~ (v1_xboole_0 @ X25)
% 1.74/1.98          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X27)))
% 1.74/1.98          | (v1_xboole_0 @ X26))),
% 1.74/1.98      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.74/1.98  thf('61', plain,
% 1.74/1.98      ((((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.74/1.98         <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['59', '60'])).
% 1.74/1.98  thf(t66_xboole_1, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 1.74/1.98       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.74/1.98  thf('62', plain,
% 1.74/1.98      (![X14 : $i]: ((r1_xboole_0 @ X14 @ X14) | ((X14) != (k1_xboole_0)))),
% 1.74/1.98      inference('cnf', [status(esa)], [t66_xboole_1])).
% 1.74/1.98  thf('63', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 1.74/1.98      inference('simplify', [status(thm)], ['62'])).
% 1.74/1.98  thf(d1_xboole_0, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.74/1.98  thf('64', plain,
% 1.74/1.98      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.74/1.98      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.74/1.98  thf('65', plain,
% 1.74/1.98      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.74/1.98      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.74/1.98  thf(t3_xboole_0, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.74/1.98            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.74/1.98       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.74/1.98            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.74/1.98  thf('66', plain,
% 1.74/1.98      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X6 @ X4)
% 1.74/1.98          | ~ (r2_hidden @ X6 @ X7)
% 1.74/1.98          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.74/1.98      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.74/1.98  thf('67', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((v1_xboole_0 @ X0)
% 1.74/1.98          | ~ (r1_xboole_0 @ X0 @ X1)
% 1.74/1.98          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 1.74/1.98      inference('sup-', [status(thm)], ['65', '66'])).
% 1.74/1.98  thf('68', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['64', '67'])).
% 1.74/1.98  thf('69', plain,
% 1.74/1.98      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 1.74/1.98      inference('simplify', [status(thm)], ['68'])).
% 1.74/1.98  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.74/1.98      inference('sup-', [status(thm)], ['63', '69'])).
% 1.74/1.98  thf('71', plain, (((v1_xboole_0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('demod', [status(thm)], ['61', '70'])).
% 1.74/1.98  thf(l13_xboole_0, axiom,
% 1.74/1.98    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.74/1.98  thf('72', plain,
% 1.74/1.98      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.74/1.98      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.74/1.98  thf('73', plain,
% 1.74/1.98      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['71', '72'])).
% 1.74/1.98  thf('74', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 1.74/1.98      inference('sup-', [status(thm)], ['0', '11'])).
% 1.74/1.98  thf('75', plain,
% 1.74/1.98      (((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ sk_C_1))
% 1.74/1.98         <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup+', [status(thm)], ['73', '74'])).
% 1.74/1.98  thf('76', plain,
% 1.74/1.98      (((m1_subset_1 @ sk_D @ 
% 1.74/1.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.74/1.98         <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup+', [status(thm)], ['57', '58'])).
% 1.74/1.98  thf('77', plain,
% 1.74/1.98      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['71', '72'])).
% 1.74/1.98  thf('78', plain,
% 1.74/1.98      (((m1_subset_1 @ k1_xboole_0 @ 
% 1.74/1.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.74/1.98         <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('demod', [status(thm)], ['76', '77'])).
% 1.74/1.98  thf('79', plain,
% 1.74/1.98      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.74/1.98         (~ (r1_tarski @ (k2_relat_1 @ X34) @ X35)
% 1.74/1.98          | (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 1.74/1.98          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 1.74/1.98      inference('cnf', [status(esa)], [t14_relset_1])).
% 1.74/1.98  thf('80', plain,
% 1.74/1.98      ((![X0 : $i]:
% 1.74/1.98          ((m1_subset_1 @ k1_xboole_0 @ 
% 1.74/1.98            (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))
% 1.74/1.98           | ~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)))
% 1.74/1.98         <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['78', '79'])).
% 1.74/1.98  thf('81', plain,
% 1.74/1.98      (((m1_subset_1 @ k1_xboole_0 @ 
% 1.74/1.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 1.74/1.98         <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['75', '80'])).
% 1.74/1.98  thf('82', plain,
% 1.74/1.98      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.74/1.98         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 1.74/1.98          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.74/1.98  thf('83', plain,
% 1.74/1.98      ((((k1_relset_1 @ k1_xboole_0 @ sk_C_1 @ k1_xboole_0)
% 1.74/1.98          = (k1_relat_1 @ k1_xboole_0)))
% 1.74/1.98         <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['81', '82'])).
% 1.74/1.98  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.74/1.98      inference('sup-', [status(thm)], ['63', '69'])).
% 1.74/1.98  thf(fc10_relat_1, axiom,
% 1.74/1.98    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 1.74/1.98  thf('85', plain,
% 1.74/1.98      (![X18 : $i]:
% 1.74/1.98         ((v1_xboole_0 @ (k1_relat_1 @ X18)) | ~ (v1_xboole_0 @ X18))),
% 1.74/1.98      inference('cnf', [status(esa)], [fc10_relat_1])).
% 1.74/1.98  thf('86', plain,
% 1.74/1.98      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.74/1.98      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.74/1.98  thf('87', plain,
% 1.74/1.98      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['85', '86'])).
% 1.74/1.98  thf('88', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['84', '87'])).
% 1.74/1.98  thf('89', plain,
% 1.74/1.98      ((((k1_relset_1 @ k1_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.74/1.98         <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('demod', [status(thm)], ['83', '88'])).
% 1.74/1.98  thf('90', plain,
% 1.74/1.98      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.74/1.98         (((X45) != (k1_relset_1 @ X45 @ X46 @ X47))
% 1.74/1.98          | (v1_funct_2 @ X47 @ X45 @ X46)
% 1.74/1.98          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.74/1.98  thf('91', plain,
% 1.74/1.98      (((((k1_xboole_0) != (k1_xboole_0))
% 1.74/1.98         | ~ (zip_tseitin_1 @ k1_xboole_0 @ sk_C_1 @ k1_xboole_0)
% 1.74/1.98         | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 1.74/1.98         <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['89', '90'])).
% 1.74/1.98  thf('92', plain,
% 1.74/1.98      ((((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)
% 1.74/1.98         | ~ (zip_tseitin_1 @ k1_xboole_0 @ sk_C_1 @ k1_xboole_0)))
% 1.74/1.98         <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('simplify', [status(thm)], ['91'])).
% 1.74/1.98  thf('93', plain,
% 1.74/1.98      (((m1_subset_1 @ k1_xboole_0 @ 
% 1.74/1.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 1.74/1.98         <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['75', '80'])).
% 1.74/1.98  thf('94', plain,
% 1.74/1.98      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.74/1.98         (~ (zip_tseitin_0 @ X48 @ X49)
% 1.74/1.98          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 1.74/1.98          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.74/1.98  thf('95', plain,
% 1.74/1.98      ((((zip_tseitin_1 @ k1_xboole_0 @ sk_C_1 @ k1_xboole_0)
% 1.74/1.98         | ~ (zip_tseitin_0 @ sk_C_1 @ k1_xboole_0)))
% 1.74/1.98         <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['93', '94'])).
% 1.74/1.98  thf('96', plain,
% 1.74/1.98      (![X43 : $i, X44 : $i]:
% 1.74/1.98         ((zip_tseitin_0 @ X43 @ X44) | ((X44) != (k1_xboole_0)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.74/1.98  thf('97', plain, (![X43 : $i]: (zip_tseitin_0 @ X43 @ k1_xboole_0)),
% 1.74/1.98      inference('simplify', [status(thm)], ['96'])).
% 1.74/1.98  thf('98', plain,
% 1.74/1.98      (((zip_tseitin_1 @ k1_xboole_0 @ sk_C_1 @ k1_xboole_0))
% 1.74/1.98         <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('demod', [status(thm)], ['95', '97'])).
% 1.74/1.98  thf('99', plain,
% 1.74/1.98      (((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))
% 1.74/1.98         <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('demod', [status(thm)], ['92', '98'])).
% 1.74/1.98  thf('100', plain,
% 1.74/1.98      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['71', '72'])).
% 1.74/1.98  thf('101', plain,
% 1.74/1.98      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('split', [status(esa)], ['55'])).
% 1.74/1.98  thf('102', plain,
% 1.74/1.98      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 1.74/1.98         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.74/1.98      inference('split', [status(esa)], ['40'])).
% 1.74/1.98  thf('103', plain,
% 1.74/1.98      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 1.74/1.98         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 1.74/1.98             (((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['101', '102'])).
% 1.74/1.98  thf('104', plain,
% 1.74/1.98      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))
% 1.74/1.98         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 1.74/1.98             (((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['100', '103'])).
% 1.74/1.98  thf('105', plain,
% 1.74/1.98      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ (((sk_A) = (k1_xboole_0)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['99', '104'])).
% 1.74/1.98  thf('106', plain,
% 1.74/1.98      (((m1_subset_1 @ k1_xboole_0 @ 
% 1.74/1.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 1.74/1.98         <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['75', '80'])).
% 1.74/1.98  thf('107', plain,
% 1.74/1.98      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['71', '72'])).
% 1.74/1.98  thf('108', plain,
% 1.74/1.98      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('split', [status(esa)], ['55'])).
% 1.74/1.98  thf('109', plain,
% 1.74/1.98      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 1.74/1.98         <= (~
% 1.74/1.98             ((m1_subset_1 @ sk_D @ 
% 1.74/1.98               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 1.74/1.98      inference('split', [status(esa)], ['40'])).
% 1.74/1.98  thf('110', plain,
% 1.74/1.98      ((~ (m1_subset_1 @ sk_D @ 
% 1.74/1.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 1.74/1.98         <= (~
% 1.74/1.98             ((m1_subset_1 @ sk_D @ 
% 1.74/1.98               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 1.74/1.98             (((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['108', '109'])).
% 1.74/1.98  thf('111', plain,
% 1.74/1.98      ((~ (m1_subset_1 @ k1_xboole_0 @ 
% 1.74/1.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 1.74/1.98         <= (~
% 1.74/1.98             ((m1_subset_1 @ sk_D @ 
% 1.74/1.98               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 1.74/1.98             (((sk_A) = (k1_xboole_0))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['107', '110'])).
% 1.74/1.98  thf('112', plain,
% 1.74/1.98      (~ (((sk_A) = (k1_xboole_0))) | 
% 1.74/1.98       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['106', '111'])).
% 1.74/1.98  thf('113', plain,
% 1.74/1.98      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 1.74/1.98       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ ((v1_funct_1 @ sk_D))),
% 1.74/1.98      inference('split', [status(esa)], ['40'])).
% 1.74/1.98  thf('114', plain,
% 1.74/1.98      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.74/1.98      inference('split', [status(esa)], ['55'])).
% 1.74/1.98  thf('115', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 1.74/1.98      inference('sat_resolution*', [status(thm)],
% 1.74/1.98                ['44', '105', '112', '113', '114'])).
% 1.74/1.98  thf('116', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.74/1.98      inference('simpl_trail', [status(thm)], ['56', '115'])).
% 1.74/1.98  thf('117', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.74/1.98      inference('simplify_reflect-', [status(thm)], ['54', '116'])).
% 1.74/1.98  thf('118', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ k1_xboole_0)),
% 1.74/1.98      inference('demod', [status(thm)], ['12', '117'])).
% 1.74/1.98  thf('119', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(t8_funct_2, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i,D:$i]:
% 1.74/1.98     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.74/1.98         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.74/1.98       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.74/1.98         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 1.74/1.98             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 1.74/1.98           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.74/1.98  thf(zf_stmt_6, type, zip_tseitin_3 : $i > $i > $o).
% 1.74/1.98  thf(zf_stmt_7, axiom,
% 1.74/1.98    (![B:$i,A:$i]:
% 1.74/1.98     ( ( zip_tseitin_3 @ B @ A ) =>
% 1.74/1.98       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 1.74/1.98  thf(zf_stmt_8, type, zip_tseitin_2 : $i > $i > $i > $o).
% 1.74/1.98  thf(zf_stmt_9, axiom,
% 1.74/1.98    (![D:$i,C:$i,A:$i]:
% 1.74/1.98     ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 1.74/1.98       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.74/1.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 1.74/1.98  thf(zf_stmt_10, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i,D:$i]:
% 1.74/1.98     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.74/1.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.74/1.98       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.74/1.98         ( ( zip_tseitin_3 @ B @ A ) | ( zip_tseitin_2 @ D @ C @ A ) ) ) ))).
% 1.74/1.98  thf('120', plain,
% 1.74/1.98      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 1.74/1.98         ((zip_tseitin_3 @ X56 @ X57)
% 1.74/1.98          | ~ (v1_funct_1 @ X58)
% 1.74/1.98          | ~ (v1_funct_2 @ X58 @ X57 @ X56)
% 1.74/1.98          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X56)))
% 1.74/1.98          | (zip_tseitin_2 @ X58 @ X59 @ X57)
% 1.74/1.98          | ~ (r1_tarski @ (k2_relset_1 @ X57 @ X56 @ X58) @ X59))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_10])).
% 1.74/1.98  thf('121', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         (~ (r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ X0)
% 1.74/1.98          | (zip_tseitin_2 @ sk_D @ X0 @ sk_A)
% 1.74/1.98          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_1)
% 1.74/1.98          | ~ (v1_funct_1 @ sk_D)
% 1.74/1.98          | (zip_tseitin_3 @ sk_B_1 @ sk_A))),
% 1.74/1.98      inference('sup-', [status(thm)], ['119', '120'])).
% 1.74/1.98  thf('122', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(redefinition_k2_relset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.98       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.74/1.98  thf('123', plain,
% 1.74/1.98      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.74/1.98         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 1.74/1.98          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.74/1.98  thf('124', plain,
% 1.74/1.98      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.74/1.98      inference('sup-', [status(thm)], ['122', '123'])).
% 1.74/1.98  thf('125', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('126', plain, ((v1_funct_1 @ sk_D)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('127', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 1.74/1.98          | (zip_tseitin_2 @ sk_D @ X0 @ sk_A)
% 1.74/1.98          | (zip_tseitin_3 @ sk_B_1 @ sk_A))),
% 1.74/1.98      inference('demod', [status(thm)], ['121', '124', '125', '126'])).
% 1.74/1.98  thf('128', plain,
% 1.74/1.98      (((zip_tseitin_3 @ sk_B_1 @ sk_A)
% 1.74/1.98        | (zip_tseitin_2 @ sk_D @ k1_xboole_0 @ sk_A))),
% 1.74/1.98      inference('sup-', [status(thm)], ['118', '127'])).
% 1.74/1.98  thf('129', plain,
% 1.74/1.98      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.74/1.98         ((v1_funct_2 @ X51 @ X53 @ X52) | ~ (zip_tseitin_2 @ X51 @ X52 @ X53))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_9])).
% 1.74/1.98  thf('130', plain,
% 1.74/1.98      (((zip_tseitin_3 @ sk_B_1 @ sk_A)
% 1.74/1.98        | (v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['128', '129'])).
% 1.74/1.98  thf('131', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 1.74/1.98      inference('simpl_trail', [status(thm)], ['41', '49'])).
% 1.74/1.98  thf('132', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.74/1.98      inference('simplify_reflect-', [status(thm)], ['54', '116'])).
% 1.74/1.98  thf('133', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0)),
% 1.74/1.98      inference('demod', [status(thm)], ['131', '132'])).
% 1.74/1.98  thf('134', plain, ((zip_tseitin_3 @ sk_B_1 @ sk_A)),
% 1.74/1.98      inference('clc', [status(thm)], ['130', '133'])).
% 1.74/1.98  thf('135', plain,
% 1.74/1.98      (![X54 : $i, X55 : $i]:
% 1.74/1.98         (((X54) = (k1_xboole_0)) | ~ (zip_tseitin_3 @ X54 @ X55))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_7])).
% 1.74/1.98  thf('136', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['134', '135'])).
% 1.74/1.98  thf('137', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.74/1.98      inference('simpl_trail', [status(thm)], ['56', '115'])).
% 1.74/1.98  thf('138', plain, ($false),
% 1.74/1.98      inference('simplify_reflect-', [status(thm)], ['136', '137'])).
% 1.74/1.98  
% 1.74/1.98  % SZS output end Refutation
% 1.74/1.98  
% 1.82/1.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
