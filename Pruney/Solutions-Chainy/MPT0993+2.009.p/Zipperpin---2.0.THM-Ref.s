%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fdaNmtVhcD

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:46 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 282 expanded)
%              Number of leaves         :   36 (  97 expanded)
%              Depth                    :   17
%              Number of atoms          :  640 (3423 expanded)
%              Number of equality atoms :   51 ( 127 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 )
        = ( k7_relat_1 @ X28 @ X31 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( v4_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('25',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( v4_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( v4_relat_1 @ sk_D @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','26'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
        = ( k7_relat_1 @ X5 @ X6 ) )
      | ~ ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['23','24'])).

thf('31',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('33',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 )
      | ( X16 != X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('36',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['33','37'])).

thf('39',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['6','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['33','37'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','43'])).

thf('45',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
        = ( k7_relat_1 @ X5 @ X6 ) )
      | ~ ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['23','24'])).

thf('52',plain,(
    ! [X0: $i] :
      ( sk_D
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['34','36'])).

thf('54',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['33','37'])).

thf('55',plain,(
    r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['39','52','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fdaNmtVhcD
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:50:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.51/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.74  % Solved by: fo/fo7.sh
% 0.51/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.74  % done 251 iterations in 0.291s
% 0.51/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.74  % SZS output start Refutation
% 0.51/0.74  thf(sk_D_type, type, sk_D: $i).
% 0.51/0.74  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.51/0.74  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.51/0.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.51/0.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.51/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.74  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.51/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.51/0.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.51/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.51/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.51/0.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.51/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.74  thf(t40_funct_2, conjecture,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.74     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.51/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.51/0.74       ( ( r1_tarski @ A @ C ) =>
% 0.51/0.74         ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ))).
% 0.51/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.74    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.74        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.51/0.74            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.51/0.74          ( ( r1_tarski @ A @ C ) =>
% 0.51/0.74            ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )),
% 0.51/0.74    inference('cnf.neg', [status(esa)], [t40_funct_2])).
% 0.51/0.74  thf('0', plain,
% 0.51/0.74      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.51/0.74          (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_D)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('1', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(redefinition_k2_partfun1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.74     ( ( ( v1_funct_1 @ C ) & 
% 0.51/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.51/0.74       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.51/0.74  thf('2', plain,
% 0.51/0.74      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.51/0.74          | ~ (v1_funct_1 @ X28)
% 0.51/0.74          | ((k2_partfun1 @ X29 @ X30 @ X28 @ X31) = (k7_relat_1 @ X28 @ X31)))),
% 0.51/0.74      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.51/0.74  thf('3', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 0.51/0.74          | ~ (v1_funct_1 @ sk_D))),
% 0.51/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.74  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('5', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.51/0.74      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.74  thf('6', plain,
% 0.51/0.74      (~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.51/0.74      inference('demod', [status(thm)], ['0', '5'])).
% 0.51/0.74  thf('7', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(d1_funct_2, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.51/0.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.51/0.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.51/0.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.51/0.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.51/0.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_1, axiom,
% 0.51/0.74    (![B:$i,A:$i]:
% 0.51/0.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.51/0.74       ( zip_tseitin_0 @ B @ A ) ))).
% 0.51/0.74  thf('8', plain,
% 0.51/0.74      (![X20 : $i, X21 : $i]:
% 0.51/0.74         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.51/0.74  thf('9', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.51/0.74  thf(zf_stmt_3, axiom,
% 0.51/0.74    (![C:$i,B:$i,A:$i]:
% 0.51/0.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.51/0.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.51/0.74  thf(zf_stmt_5, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.51/0.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.51/0.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.51/0.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.51/0.74  thf('10', plain,
% 0.51/0.74      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.51/0.74         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.51/0.74          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.51/0.74          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.51/0.74  thf('11', plain,
% 0.51/0.74      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.51/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.74  thf('12', plain,
% 0.51/0.74      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.51/0.74      inference('sup-', [status(thm)], ['8', '11'])).
% 0.51/0.74  thf('13', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('14', plain,
% 0.51/0.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.51/0.74         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.51/0.74          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.51/0.74          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.51/0.74  thf('15', plain,
% 0.51/0.74      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.51/0.74        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.51/0.74  thf('16', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(redefinition_k1_relset_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.51/0.74  thf('17', plain,
% 0.51/0.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.51/0.74         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.51/0.74          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.51/0.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.51/0.74  thf('18', plain,
% 0.51/0.74      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.51/0.74      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.74  thf('19', plain,
% 0.51/0.74      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.51/0.74      inference('demod', [status(thm)], ['15', '18'])).
% 0.51/0.74  thf('20', plain,
% 0.51/0.74      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['12', '19'])).
% 0.51/0.74  thf(d18_relat_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( v1_relat_1 @ B ) =>
% 0.51/0.74       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.51/0.74  thf('21', plain,
% 0.51/0.74      (![X3 : $i, X4 : $i]:
% 0.51/0.74         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.51/0.74          | (v4_relat_1 @ X3 @ X4)
% 0.51/0.74          | ~ (v1_relat_1 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.51/0.74  thf('22', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         (~ (r1_tarski @ sk_A @ X0)
% 0.51/0.74          | ((sk_B) = (k1_xboole_0))
% 0.51/0.74          | ~ (v1_relat_1 @ sk_D)
% 0.51/0.74          | (v4_relat_1 @ sk_D @ X0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['20', '21'])).
% 0.51/0.74  thf('23', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(cc1_relset_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( v1_relat_1 @ C ) ))).
% 0.51/0.74  thf('24', plain,
% 0.51/0.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.51/0.74         ((v1_relat_1 @ X7)
% 0.51/0.74          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.51/0.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.51/0.74  thf('25', plain, ((v1_relat_1 @ sk_D)),
% 0.51/0.74      inference('sup-', [status(thm)], ['23', '24'])).
% 0.51/0.74  thf('26', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         (~ (r1_tarski @ sk_A @ X0)
% 0.51/0.74          | ((sk_B) = (k1_xboole_0))
% 0.51/0.74          | (v4_relat_1 @ sk_D @ X0))),
% 0.51/0.74      inference('demod', [status(thm)], ['22', '25'])).
% 0.51/0.74  thf('27', plain, (((v4_relat_1 @ sk_D @ sk_C) | ((sk_B) = (k1_xboole_0)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['7', '26'])).
% 0.51/0.74  thf(t209_relat_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.51/0.74       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.51/0.74  thf('28', plain,
% 0.51/0.74      (![X5 : $i, X6 : $i]:
% 0.51/0.74         (((X5) = (k7_relat_1 @ X5 @ X6))
% 0.51/0.74          | ~ (v4_relat_1 @ X5 @ X6)
% 0.51/0.74          | ~ (v1_relat_1 @ X5))),
% 0.51/0.74      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.51/0.74  thf('29', plain,
% 0.51/0.74      ((((sk_B) = (k1_xboole_0))
% 0.51/0.74        | ~ (v1_relat_1 @ sk_D)
% 0.51/0.74        | ((sk_D) = (k7_relat_1 @ sk_D @ sk_C)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['27', '28'])).
% 0.51/0.74  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.51/0.74      inference('sup-', [status(thm)], ['23', '24'])).
% 0.51/0.74  thf('31', plain,
% 0.51/0.74      ((((sk_B) = (k1_xboole_0)) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_C)))),
% 0.51/0.74      inference('demod', [status(thm)], ['29', '30'])).
% 0.51/0.74  thf('32', plain,
% 0.51/0.74      (~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.51/0.74      inference('demod', [status(thm)], ['0', '5'])).
% 0.51/0.74  thf('33', plain,
% 0.51/0.74      ((~ (r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D) | ((sk_B) = (k1_xboole_0)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['31', '32'])).
% 0.51/0.74  thf('34', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(redefinition_r2_relset_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.74     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.51/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.51/0.74       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.51/0.74  thf('35', plain,
% 0.51/0.74      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.51/0.74          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.51/0.74          | (r2_relset_1 @ X17 @ X18 @ X16 @ X19)
% 0.51/0.74          | ((X16) != (X19)))),
% 0.51/0.74      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.51/0.74  thf('36', plain,
% 0.51/0.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.51/0.74         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 0.51/0.74          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['35'])).
% 0.51/0.74  thf('37', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.51/0.74      inference('sup-', [status(thm)], ['34', '36'])).
% 0.51/0.74  thf('38', plain, (((sk_B) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['33', '37'])).
% 0.51/0.74  thf('39', plain,
% 0.51/0.74      (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.51/0.74      inference('demod', [status(thm)], ['6', '38'])).
% 0.51/0.74  thf('40', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('41', plain, (((sk_B) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['33', '37'])).
% 0.51/0.74  thf(t113_zfmisc_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.51/0.74       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.51/0.74  thf('42', plain,
% 0.51/0.74      (![X1 : $i, X2 : $i]:
% 0.51/0.74         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.51/0.74  thf('43', plain,
% 0.51/0.74      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.51/0.74      inference('simplify', [status(thm)], ['42'])).
% 0.51/0.74  thf('44', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['40', '41', '43'])).
% 0.51/0.74  thf('45', plain,
% 0.51/0.74      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.51/0.74      inference('simplify', [status(thm)], ['42'])).
% 0.51/0.74  thf(cc2_relset_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.51/0.74  thf('46', plain,
% 0.51/0.74      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.51/0.74         ((v4_relat_1 @ X10 @ X11)
% 0.51/0.74          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.51/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.51/0.74  thf('47', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.51/0.74          | (v4_relat_1 @ X1 @ X0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['45', '46'])).
% 0.51/0.74  thf('48', plain, (![X0 : $i]: (v4_relat_1 @ sk_D @ X0)),
% 0.51/0.74      inference('sup-', [status(thm)], ['44', '47'])).
% 0.51/0.74  thf('49', plain,
% 0.51/0.74      (![X5 : $i, X6 : $i]:
% 0.51/0.74         (((X5) = (k7_relat_1 @ X5 @ X6))
% 0.51/0.74          | ~ (v4_relat_1 @ X5 @ X6)
% 0.51/0.74          | ~ (v1_relat_1 @ X5))),
% 0.51/0.74      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.51/0.74  thf('50', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         (~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ X0)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['48', '49'])).
% 0.51/0.74  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 0.51/0.74      inference('sup-', [status(thm)], ['23', '24'])).
% 0.51/0.74  thf('52', plain, (![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0))),
% 0.51/0.74      inference('demod', [status(thm)], ['50', '51'])).
% 0.51/0.74  thf('53', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.51/0.74      inference('sup-', [status(thm)], ['34', '36'])).
% 0.51/0.74  thf('54', plain, (((sk_B) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['33', '37'])).
% 0.51/0.74  thf('55', plain, ((r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D @ sk_D)),
% 0.51/0.74      inference('demod', [status(thm)], ['53', '54'])).
% 0.51/0.74  thf('56', plain, ($false),
% 0.51/0.74      inference('demod', [status(thm)], ['39', '52', '55'])).
% 0.51/0.74  
% 0.51/0.74  % SZS output end Refutation
% 0.51/0.74  
% 0.51/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
