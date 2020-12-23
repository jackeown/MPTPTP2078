%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xQUfM1K2KR

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:50 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 482 expanded)
%              Number of leaves         :   41 ( 157 expanded)
%              Depth                    :   17
%              Number of atoms          :  929 (5781 expanded)
%              Number of equality atoms :   78 ( 236 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t40_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ A @ C )
       => ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ A @ C )
         => ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ( ( k2_partfun1 @ X43 @ X44 @ X42 @ X45 )
        = ( k7_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_C ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['25','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ sk_B @ X1 )
      | ( r1_tarski @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( r1_tarski @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ~ ( r1_tarski @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_B = sk_D )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','38'])).

thf('40',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('41',plain,
    ( ( sk_B = sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('43',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_B = sk_D ) ),
    inference(clc,[status(thm)],['41','42'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('44',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ( ( k7_relat_1 @ X22 @ X23 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = sk_D )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k7_relat_1 @ sk_D @ X0 )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = sk_D )
      | ( ( k7_relat_1 @ sk_D @ X0 )
        = sk_D ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,
    ( ( ( k7_relat_1 @ sk_D @ sk_C )
      = sk_D )
    | ( sk_B = sk_D ) ),
    inference('sup-',[status(thm)],['7','51'])).

thf('53',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('54',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D )
    | ( sk_B = sk_D ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('56',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( r2_relset_1 @ X31 @ X32 @ X30 @ X33 )
      | ( X30 != X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('57',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_relset_1 @ X31 @ X32 @ X33 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    sk_B = sk_D ),
    inference(demod,[status(thm)],['54','58'])).

thf('60',plain,(
    sk_B = sk_D ),
    inference(demod,[status(thm)],['54','58'])).

thf('61',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','59','60'])).

thf('62',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('65',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('67',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ( ( k7_relat_1 @ X22 @ X23 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k7_relat_1 @ sk_D @ X0 )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( ( k7_relat_1 @ sk_D @ X0 )
        = sk_D ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k7_relat_1 @ sk_D @ sk_C )
      = sk_D )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','71'])).

thf('73',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('74',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['55','57'])).

thf('76',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75'])).

thf('78',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('79',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('80',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('81',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X20
        = ( k7_relat_1 @ X20 @ X21 ) )
      | ~ ( v4_relat_1 @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('84',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('86',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','86'])).

thf('88',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75'])).

thf('89',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('90',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_relset_1 @ X31 @ X32 @ X33 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['61','76','77','87','88','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xQUfM1K2KR
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:26:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.55/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.76  % Solved by: fo/fo7.sh
% 0.55/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.76  % done 430 iterations in 0.298s
% 0.55/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.76  % SZS output start Refutation
% 0.55/0.76  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.55/0.76  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.55/0.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.76  thf(sk_D_type, type, sk_D: $i).
% 0.55/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.55/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.76  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.55/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.76  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.55/0.76  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.55/0.76  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.55/0.76  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.55/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.76  thf(t40_funct_2, conjecture,
% 0.55/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.76     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.55/0.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.76       ( ( r1_tarski @ A @ C ) =>
% 0.55/0.76         ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ))).
% 0.55/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.76    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.76        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.55/0.76            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.76          ( ( r1_tarski @ A @ C ) =>
% 0.55/0.76            ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )),
% 0.55/0.76    inference('cnf.neg', [status(esa)], [t40_funct_2])).
% 0.55/0.76  thf('0', plain,
% 0.55/0.76      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.55/0.76          (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_D)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('1', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf(redefinition_k2_partfun1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.76     ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.76       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.55/0.76  thf('2', plain,
% 0.55/0.76      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.55/0.76         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.55/0.76          | ~ (v1_funct_1 @ X42)
% 0.55/0.76          | ((k2_partfun1 @ X43 @ X44 @ X42 @ X45) = (k7_relat_1 @ X42 @ X45)))),
% 0.55/0.76      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.55/0.76  thf('3', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 0.55/0.76          | ~ (v1_funct_1 @ sk_D))),
% 0.55/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.76  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('5', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.55/0.76      inference('demod', [status(thm)], ['3', '4'])).
% 0.55/0.76  thf('6', plain,
% 0.55/0.76      (~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.55/0.76      inference('demod', [status(thm)], ['0', '5'])).
% 0.55/0.76  thf('7', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf(d1_funct_2, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.76       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.55/0.76           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.55/0.76             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.55/0.76         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.55/0.76           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.55/0.76             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.55/0.76  thf(zf_stmt_1, axiom,
% 0.55/0.76    (![B:$i,A:$i]:
% 0.55/0.76     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.55/0.76       ( zip_tseitin_0 @ B @ A ) ))).
% 0.55/0.76  thf('8', plain,
% 0.55/0.76      (![X34 : $i, X35 : $i]:
% 0.55/0.76         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.55/0.76  thf(t4_subset_1, axiom,
% 0.55/0.76    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.55/0.76  thf('9', plain,
% 0.55/0.76      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.55/0.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.55/0.76  thf(t3_subset, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.55/0.76  thf('10', plain,
% 0.55/0.76      (![X10 : $i, X11 : $i]:
% 0.55/0.76         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.55/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.55/0.76  thf('11', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.55/0.76      inference('sup-', [status(thm)], ['9', '10'])).
% 0.55/0.76  thf('12', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.76         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.55/0.76      inference('sup+', [status(thm)], ['8', '11'])).
% 0.55/0.76  thf('13', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.55/0.76  thf(zf_stmt_3, axiom,
% 0.55/0.76    (![C:$i,B:$i,A:$i]:
% 0.55/0.76     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.55/0.76       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.55/0.76  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.55/0.76  thf(zf_stmt_5, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.76       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.55/0.76         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.55/0.76           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.55/0.76             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.55/0.76  thf('14', plain,
% 0.55/0.76      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.55/0.76         (~ (zip_tseitin_0 @ X39 @ X40)
% 0.55/0.76          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 0.55/0.76          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.55/0.76  thf('15', plain,
% 0.55/0.76      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['13', '14'])).
% 0.55/0.76  thf('16', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['12', '15'])).
% 0.55/0.76  thf('17', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('18', plain,
% 0.55/0.76      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.55/0.76         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 0.55/0.76          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 0.55/0.76          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.55/0.76  thf('19', plain,
% 0.55/0.76      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.55/0.76        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['17', '18'])).
% 0.55/0.76  thf('20', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf(redefinition_k1_relset_1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.76       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.55/0.76  thf('21', plain,
% 0.55/0.76      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.55/0.76         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.55/0.76          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.55/0.76      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.55/0.76  thf('22', plain,
% 0.55/0.76      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.55/0.76      inference('sup-', [status(thm)], ['20', '21'])).
% 0.55/0.76  thf('23', plain,
% 0.55/0.76      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.55/0.76      inference('demod', [status(thm)], ['19', '22'])).
% 0.55/0.76  thf('24', plain,
% 0.55/0.76      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['16', '23'])).
% 0.55/0.76  thf('25', plain,
% 0.55/0.76      (![X34 : $i, X35 : $i]:
% 0.55/0.76         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.55/0.76  thf(t113_zfmisc_1, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.55/0.76       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.55/0.76  thf('26', plain,
% 0.55/0.76      (![X7 : $i, X8 : $i]:
% 0.55/0.76         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.55/0.76      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.55/0.76  thf('27', plain,
% 0.55/0.76      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.76      inference('simplify', [status(thm)], ['26'])).
% 0.55/0.76  thf('28', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.76         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.55/0.76      inference('sup+', [status(thm)], ['25', '27'])).
% 0.55/0.76  thf('29', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('30', plain,
% 0.55/0.76      (![X10 : $i, X11 : $i]:
% 0.55/0.76         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.55/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.55/0.76  thf('31', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.55/0.76      inference('sup-', [status(thm)], ['29', '30'])).
% 0.55/0.76  thf(t1_xboole_1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.55/0.76       ( r1_tarski @ A @ C ) ))).
% 0.55/0.76  thf('32', plain,
% 0.55/0.76      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.55/0.76         (~ (r1_tarski @ X3 @ X4)
% 0.55/0.76          | ~ (r1_tarski @ X4 @ X5)
% 0.55/0.76          | (r1_tarski @ X3 @ X5))),
% 0.55/0.76      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.55/0.76  thf('33', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((r1_tarski @ sk_D @ X0)
% 0.55/0.76          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0))),
% 0.55/0.76      inference('sup-', [status(thm)], ['31', '32'])).
% 0.55/0.76  thf('34', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.55/0.76          | (zip_tseitin_0 @ sk_B @ X1)
% 0.55/0.76          | (r1_tarski @ sk_D @ X0))),
% 0.55/0.76      inference('sup-', [status(thm)], ['28', '33'])).
% 0.55/0.76  thf('35', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.55/0.76      inference('sup-', [status(thm)], ['9', '10'])).
% 0.55/0.76  thf('36', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         ((zip_tseitin_0 @ sk_B @ X1) | (r1_tarski @ sk_D @ X0))),
% 0.55/0.76      inference('demod', [status(thm)], ['34', '35'])).
% 0.55/0.76  thf(d10_xboole_0, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.76  thf('37', plain,
% 0.55/0.76      (![X0 : $i, X2 : $i]:
% 0.55/0.76         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.55/0.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.76  thf('38', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         ((zip_tseitin_0 @ sk_B @ X1)
% 0.55/0.76          | ~ (r1_tarski @ X0 @ sk_D)
% 0.55/0.76          | ((X0) = (sk_D)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['36', '37'])).
% 0.55/0.76  thf('39', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (((sk_A) = (k1_relat_1 @ sk_D))
% 0.55/0.76          | ((sk_B) = (sk_D))
% 0.55/0.76          | (zip_tseitin_0 @ sk_B @ X0))),
% 0.55/0.76      inference('sup-', [status(thm)], ['24', '38'])).
% 0.55/0.76  thf('40', plain,
% 0.55/0.76      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['13', '14'])).
% 0.55/0.76  thf('41', plain,
% 0.55/0.76      ((((sk_B) = (sk_D))
% 0.55/0.76        | ((sk_A) = (k1_relat_1 @ sk_D))
% 0.55/0.76        | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['39', '40'])).
% 0.55/0.76  thf('42', plain,
% 0.55/0.76      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.55/0.76      inference('demod', [status(thm)], ['19', '22'])).
% 0.55/0.76  thf('43', plain, ((((sk_A) = (k1_relat_1 @ sk_D)) | ((sk_B) = (sk_D)))),
% 0.55/0.76      inference('clc', [status(thm)], ['41', '42'])).
% 0.55/0.76  thf(t97_relat_1, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( v1_relat_1 @ B ) =>
% 0.55/0.76       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.55/0.76         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.55/0.76  thf('44', plain,
% 0.55/0.76      (![X22 : $i, X23 : $i]:
% 0.55/0.76         (~ (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 0.55/0.76          | ((k7_relat_1 @ X22 @ X23) = (X22))
% 0.55/0.76          | ~ (v1_relat_1 @ X22))),
% 0.55/0.76      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.55/0.76  thf('45', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (r1_tarski @ sk_A @ X0)
% 0.55/0.76          | ((sk_B) = (sk_D))
% 0.55/0.76          | ~ (v1_relat_1 @ sk_D)
% 0.55/0.76          | ((k7_relat_1 @ sk_D @ X0) = (sk_D)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['43', '44'])).
% 0.55/0.76  thf('46', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf(cc2_relat_1, axiom,
% 0.55/0.76    (![A:$i]:
% 0.55/0.76     ( ( v1_relat_1 @ A ) =>
% 0.55/0.76       ( ![B:$i]:
% 0.55/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.55/0.76  thf('47', plain,
% 0.55/0.76      (![X16 : $i, X17 : $i]:
% 0.55/0.76         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.55/0.76          | (v1_relat_1 @ X16)
% 0.55/0.76          | ~ (v1_relat_1 @ X17))),
% 0.55/0.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.55/0.76  thf('48', plain,
% 0.55/0.76      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.55/0.76      inference('sup-', [status(thm)], ['46', '47'])).
% 0.55/0.76  thf(fc6_relat_1, axiom,
% 0.55/0.76    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.55/0.76  thf('49', plain,
% 0.55/0.76      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.55/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.55/0.76  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 0.55/0.76      inference('demod', [status(thm)], ['48', '49'])).
% 0.55/0.76  thf('51', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (r1_tarski @ sk_A @ X0)
% 0.55/0.76          | ((sk_B) = (sk_D))
% 0.55/0.76          | ((k7_relat_1 @ sk_D @ X0) = (sk_D)))),
% 0.55/0.76      inference('demod', [status(thm)], ['45', '50'])).
% 0.55/0.76  thf('52', plain,
% 0.55/0.76      ((((k7_relat_1 @ sk_D @ sk_C) = (sk_D)) | ((sk_B) = (sk_D)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['7', '51'])).
% 0.55/0.76  thf('53', plain,
% 0.55/0.76      (~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.55/0.76      inference('demod', [status(thm)], ['0', '5'])).
% 0.55/0.76  thf('54', plain,
% 0.55/0.76      ((~ (r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D) | ((sk_B) = (sk_D)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['52', '53'])).
% 0.55/0.76  thf('55', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf(redefinition_r2_relset_1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.76     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.55/0.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.76       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.55/0.76  thf('56', plain,
% 0.55/0.76      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.55/0.76         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.55/0.76          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.55/0.76          | (r2_relset_1 @ X31 @ X32 @ X30 @ X33)
% 0.55/0.76          | ((X30) != (X33)))),
% 0.55/0.76      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.55/0.76  thf('57', plain,
% 0.55/0.76      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.55/0.76         ((r2_relset_1 @ X31 @ X32 @ X33 @ X33)
% 0.55/0.76          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.55/0.76      inference('simplify', [status(thm)], ['56'])).
% 0.55/0.76  thf('58', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.55/0.76      inference('sup-', [status(thm)], ['55', '57'])).
% 0.55/0.76  thf('59', plain, (((sk_B) = (sk_D))),
% 0.55/0.76      inference('demod', [status(thm)], ['54', '58'])).
% 0.55/0.76  thf('60', plain, (((sk_B) = (sk_D))),
% 0.55/0.76      inference('demod', [status(thm)], ['54', '58'])).
% 0.55/0.76  thf('61', plain,
% 0.55/0.76      (~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_B @ sk_C) @ sk_B)),
% 0.55/0.76      inference('demod', [status(thm)], ['6', '59', '60'])).
% 0.55/0.76  thf('62', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('63', plain,
% 0.55/0.76      (![X34 : $i, X35 : $i]:
% 0.55/0.76         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.55/0.76  thf('64', plain,
% 0.55/0.76      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['13', '14'])).
% 0.55/0.76  thf('65', plain,
% 0.55/0.76      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['63', '64'])).
% 0.55/0.76  thf('66', plain,
% 0.55/0.76      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.55/0.76      inference('demod', [status(thm)], ['19', '22'])).
% 0.55/0.76  thf('67', plain,
% 0.55/0.76      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['65', '66'])).
% 0.55/0.76  thf('68', plain,
% 0.55/0.76      (![X22 : $i, X23 : $i]:
% 0.55/0.76         (~ (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 0.55/0.76          | ((k7_relat_1 @ X22 @ X23) = (X22))
% 0.55/0.76          | ~ (v1_relat_1 @ X22))),
% 0.55/0.76      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.55/0.76  thf('69', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (r1_tarski @ sk_A @ X0)
% 0.55/0.76          | ((sk_B) = (k1_xboole_0))
% 0.55/0.76          | ~ (v1_relat_1 @ sk_D)
% 0.55/0.76          | ((k7_relat_1 @ sk_D @ X0) = (sk_D)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['67', '68'])).
% 0.55/0.76  thf('70', plain, ((v1_relat_1 @ sk_D)),
% 0.55/0.76      inference('demod', [status(thm)], ['48', '49'])).
% 0.55/0.76  thf('71', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (r1_tarski @ sk_A @ X0)
% 0.55/0.76          | ((sk_B) = (k1_xboole_0))
% 0.55/0.76          | ((k7_relat_1 @ sk_D @ X0) = (sk_D)))),
% 0.55/0.76      inference('demod', [status(thm)], ['69', '70'])).
% 0.55/0.76  thf('72', plain,
% 0.55/0.76      ((((k7_relat_1 @ sk_D @ sk_C) = (sk_D)) | ((sk_B) = (k1_xboole_0)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['62', '71'])).
% 0.55/0.76  thf('73', plain,
% 0.55/0.76      (~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.55/0.76      inference('demod', [status(thm)], ['0', '5'])).
% 0.55/0.76  thf('74', plain,
% 0.55/0.76      ((~ (r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D) | ((sk_B) = (k1_xboole_0)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['72', '73'])).
% 0.55/0.76  thf('75', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.55/0.76      inference('sup-', [status(thm)], ['55', '57'])).
% 0.55/0.76  thf('76', plain, (((sk_B) = (k1_xboole_0))),
% 0.55/0.76      inference('demod', [status(thm)], ['74', '75'])).
% 0.55/0.76  thf('77', plain, (((sk_B) = (k1_xboole_0))),
% 0.55/0.76      inference('demod', [status(thm)], ['74', '75'])).
% 0.55/0.76  thf('78', plain,
% 0.55/0.76      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.55/0.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.55/0.76  thf(cc2_relset_1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.55/0.76  thf('79', plain,
% 0.55/0.76      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.55/0.76         ((v4_relat_1 @ X24 @ X25)
% 0.55/0.76          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.55/0.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.55/0.76  thf('80', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.55/0.76      inference('sup-', [status(thm)], ['78', '79'])).
% 0.55/0.76  thf(t209_relat_1, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.55/0.76       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.55/0.76  thf('81', plain,
% 0.55/0.76      (![X20 : $i, X21 : $i]:
% 0.55/0.76         (((X20) = (k7_relat_1 @ X20 @ X21))
% 0.55/0.76          | ~ (v4_relat_1 @ X20 @ X21)
% 0.55/0.76          | ~ (v1_relat_1 @ X20))),
% 0.55/0.76      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.55/0.76  thf('82', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (v1_relat_1 @ k1_xboole_0)
% 0.55/0.76          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['80', '81'])).
% 0.55/0.76  thf('83', plain,
% 0.55/0.76      (![X7 : $i, X8 : $i]:
% 0.55/0.76         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.55/0.76      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.55/0.76  thf('84', plain,
% 0.55/0.76      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.55/0.76      inference('simplify', [status(thm)], ['83'])).
% 0.55/0.76  thf('85', plain,
% 0.55/0.76      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.55/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.55/0.76  thf('86', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.55/0.76      inference('sup+', [status(thm)], ['84', '85'])).
% 0.55/0.76  thf('87', plain,
% 0.55/0.76      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 0.55/0.76      inference('demod', [status(thm)], ['82', '86'])).
% 0.55/0.76  thf('88', plain, (((sk_B) = (k1_xboole_0))),
% 0.55/0.76      inference('demod', [status(thm)], ['74', '75'])).
% 0.55/0.76  thf('89', plain,
% 0.55/0.76      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.55/0.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.55/0.76  thf('90', plain,
% 0.55/0.76      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.55/0.76         ((r2_relset_1 @ X31 @ X32 @ X33 @ X33)
% 0.55/0.76          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.55/0.76      inference('simplify', [status(thm)], ['56'])).
% 0.55/0.76  thf('91', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.55/0.76      inference('sup-', [status(thm)], ['89', '90'])).
% 0.55/0.76  thf('92', plain, ($false),
% 0.55/0.76      inference('demod', [status(thm)], ['61', '76', '77', '87', '88', '91'])).
% 0.55/0.76  
% 0.55/0.76  % SZS output end Refutation
% 0.55/0.76  
% 0.55/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
