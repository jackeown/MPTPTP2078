%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.50YeAKtFGr

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:48 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 252 expanded)
%              Number of leaves         :   36 (  88 expanded)
%              Depth                    :   15
%              Number of atoms          :  620 (3123 expanded)
%              Number of equality atoms :   51 ( 124 expanded)
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

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( ( k7_relat_1 @ X5 @ X6 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k7_relat_1 @ sk_D @ X0 )
        = sk_D ) ) ),
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
      | ( ( k7_relat_1 @ sk_D @ X0 )
        = sk_D ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( ( k7_relat_1 @ sk_D @ sk_C )
      = sk_D )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','26'])).

thf('28',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('29',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 )
      | ( X16 != X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','33'])).

thf('35',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['6','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','33'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('38',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3
        = ( k7_relat_1 @ X3 @ X4 ) )
      | ~ ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['23','24'])).

thf('48',plain,(
    ! [X0: $i] :
      ( sk_D
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['30','32'])).

thf('50',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','33'])).

thf('51',plain,(
    r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['35','48','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.50YeAKtFGr
% 0.11/0.33  % Computer   : n013.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 16:00:40 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.44/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.65  % Solved by: fo/fo7.sh
% 0.44/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.65  % done 213 iterations in 0.215s
% 0.44/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.65  % SZS output start Refutation
% 0.44/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.65  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.44/0.65  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.44/0.65  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.65  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.44/0.65  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.44/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.44/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.65  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.44/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.65  thf(t40_funct_2, conjecture,
% 0.44/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.65     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.65       ( ( r1_tarski @ A @ C ) =>
% 0.44/0.65         ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ))).
% 0.44/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.65    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.65        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.65            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.65          ( ( r1_tarski @ A @ C ) =>
% 0.44/0.65            ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )),
% 0.44/0.65    inference('cnf.neg', [status(esa)], [t40_funct_2])).
% 0.44/0.65  thf('0', plain,
% 0.44/0.65      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.44/0.65          (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('1', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(redefinition_k2_partfun1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.65     ( ( ( v1_funct_1 @ C ) & 
% 0.44/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.65       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.44/0.65  thf('2', plain,
% 0.44/0.65      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.44/0.65          | ~ (v1_funct_1 @ X28)
% 0.44/0.65          | ((k2_partfun1 @ X29 @ X30 @ X28 @ X31) = (k7_relat_1 @ X28 @ X31)))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.44/0.65  thf('3', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 0.44/0.65          | ~ (v1_funct_1 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.65  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('5', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['3', '4'])).
% 0.44/0.65  thf('6', plain,
% 0.44/0.65      (~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.44/0.65      inference('demod', [status(thm)], ['0', '5'])).
% 0.44/0.65  thf('7', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(d1_funct_2, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.65           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.44/0.65             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.44/0.65         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.65           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.44/0.65             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.44/0.65  thf(zf_stmt_1, axiom,
% 0.44/0.65    (![B:$i,A:$i]:
% 0.44/0.65     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.65       ( zip_tseitin_0 @ B @ A ) ))).
% 0.44/0.65  thf('8', plain,
% 0.44/0.65      (![X20 : $i, X21 : $i]:
% 0.44/0.65         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.65  thf('9', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.44/0.65  thf(zf_stmt_3, axiom,
% 0.44/0.65    (![C:$i,B:$i,A:$i]:
% 0.44/0.65     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.44/0.65       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.44/0.65  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.44/0.65  thf(zf_stmt_5, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.44/0.65         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.65           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.65             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.44/0.65  thf('10', plain,
% 0.44/0.65      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.44/0.65         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.44/0.65          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.44/0.65          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.65  thf('11', plain,
% 0.44/0.65      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.44/0.65      inference('sup-', [status(thm)], ['9', '10'])).
% 0.44/0.65  thf('12', plain,
% 0.44/0.65      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.44/0.65      inference('sup-', [status(thm)], ['8', '11'])).
% 0.44/0.65  thf('13', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('14', plain,
% 0.44/0.65      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.44/0.65         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.44/0.65          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.44/0.65          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.65  thf('15', plain,
% 0.44/0.65      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.44/0.65        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.65  thf('16', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(redefinition_k1_relset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.44/0.65  thf('17', plain,
% 0.44/0.65      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.44/0.65         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.44/0.65          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.65  thf('18', plain,
% 0.44/0.65      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['16', '17'])).
% 0.44/0.65  thf('19', plain,
% 0.44/0.65      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.44/0.65      inference('demod', [status(thm)], ['15', '18'])).
% 0.44/0.65  thf('20', plain,
% 0.44/0.65      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['12', '19'])).
% 0.44/0.65  thf(t97_relat_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( v1_relat_1 @ B ) =>
% 0.44/0.65       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.44/0.65         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.44/0.65  thf('21', plain,
% 0.44/0.65      (![X5 : $i, X6 : $i]:
% 0.44/0.65         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.44/0.65          | ((k7_relat_1 @ X5 @ X6) = (X5))
% 0.44/0.65          | ~ (v1_relat_1 @ X5))),
% 0.44/0.65      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.44/0.65  thf('22', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r1_tarski @ sk_A @ X0)
% 0.44/0.65          | ((sk_B) = (k1_xboole_0))
% 0.44/0.65          | ~ (v1_relat_1 @ sk_D)
% 0.44/0.65          | ((k7_relat_1 @ sk_D @ X0) = (sk_D)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['20', '21'])).
% 0.44/0.65  thf('23', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(cc1_relset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( v1_relat_1 @ C ) ))).
% 0.44/0.65  thf('24', plain,
% 0.44/0.65      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.65         ((v1_relat_1 @ X7)
% 0.44/0.65          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.65  thf('25', plain, ((v1_relat_1 @ sk_D)),
% 0.44/0.65      inference('sup-', [status(thm)], ['23', '24'])).
% 0.44/0.65  thf('26', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r1_tarski @ sk_A @ X0)
% 0.44/0.65          | ((sk_B) = (k1_xboole_0))
% 0.44/0.65          | ((k7_relat_1 @ sk_D @ X0) = (sk_D)))),
% 0.44/0.65      inference('demod', [status(thm)], ['22', '25'])).
% 0.44/0.65  thf('27', plain,
% 0.44/0.65      ((((k7_relat_1 @ sk_D @ sk_C) = (sk_D)) | ((sk_B) = (k1_xboole_0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['7', '26'])).
% 0.44/0.65  thf('28', plain,
% 0.44/0.65      (~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.44/0.65      inference('demod', [status(thm)], ['0', '5'])).
% 0.44/0.65  thf('29', plain,
% 0.44/0.65      ((~ (r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D) | ((sk_B) = (k1_xboole_0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.44/0.65  thf('30', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(redefinition_r2_relset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.65     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.44/0.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.65       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.44/0.65  thf('31', plain,
% 0.44/0.65      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.44/0.65          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.44/0.65          | (r2_relset_1 @ X17 @ X18 @ X16 @ X19)
% 0.44/0.65          | ((X16) != (X19)))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.44/0.65  thf('32', plain,
% 0.44/0.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.44/0.65         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 0.44/0.65          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.44/0.65      inference('simplify', [status(thm)], ['31'])).
% 0.44/0.65  thf('33', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.44/0.65      inference('sup-', [status(thm)], ['30', '32'])).
% 0.44/0.65  thf('34', plain, (((sk_B) = (k1_xboole_0))),
% 0.44/0.65      inference('demod', [status(thm)], ['29', '33'])).
% 0.44/0.65  thf('35', plain,
% 0.44/0.65      (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.44/0.65      inference('demod', [status(thm)], ['6', '34'])).
% 0.44/0.65  thf('36', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('37', plain, (((sk_B) = (k1_xboole_0))),
% 0.44/0.65      inference('demod', [status(thm)], ['29', '33'])).
% 0.44/0.65  thf(t113_zfmisc_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.44/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.44/0.65  thf('38', plain,
% 0.44/0.65      (![X1 : $i, X2 : $i]:
% 0.44/0.65         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.44/0.65  thf('39', plain,
% 0.44/0.65      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.65      inference('simplify', [status(thm)], ['38'])).
% 0.44/0.65  thf('40', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.44/0.65      inference('demod', [status(thm)], ['36', '37', '39'])).
% 0.44/0.65  thf('41', plain,
% 0.44/0.65      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.65      inference('simplify', [status(thm)], ['38'])).
% 0.44/0.65  thf(cc2_relset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.65  thf('42', plain,
% 0.44/0.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.65         ((v4_relat_1 @ X10 @ X11)
% 0.44/0.65          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.65  thf('43', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.44/0.65          | (v4_relat_1 @ X1 @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['41', '42'])).
% 0.44/0.65  thf('44', plain, (![X0 : $i]: (v4_relat_1 @ sk_D @ X0)),
% 0.44/0.65      inference('sup-', [status(thm)], ['40', '43'])).
% 0.44/0.65  thf(t209_relat_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.44/0.65       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.44/0.65  thf('45', plain,
% 0.44/0.65      (![X3 : $i, X4 : $i]:
% 0.44/0.65         (((X3) = (k7_relat_1 @ X3 @ X4))
% 0.44/0.65          | ~ (v4_relat_1 @ X3 @ X4)
% 0.44/0.65          | ~ (v1_relat_1 @ X3))),
% 0.44/0.65      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.44/0.65  thf('46', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ X0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.44/0.65  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 0.44/0.65      inference('sup-', [status(thm)], ['23', '24'])).
% 0.44/0.65  thf('48', plain, (![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['46', '47'])).
% 0.44/0.65  thf('49', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.44/0.65      inference('sup-', [status(thm)], ['30', '32'])).
% 0.44/0.65  thf('50', plain, (((sk_B) = (k1_xboole_0))),
% 0.44/0.65      inference('demod', [status(thm)], ['29', '33'])).
% 0.44/0.65  thf('51', plain, ((r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D @ sk_D)),
% 0.44/0.65      inference('demod', [status(thm)], ['49', '50'])).
% 0.44/0.65  thf('52', plain, ($false),
% 0.44/0.65      inference('demod', [status(thm)], ['35', '48', '51'])).
% 0.44/0.65  
% 0.44/0.65  % SZS output end Refutation
% 0.44/0.65  
% 0.44/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
