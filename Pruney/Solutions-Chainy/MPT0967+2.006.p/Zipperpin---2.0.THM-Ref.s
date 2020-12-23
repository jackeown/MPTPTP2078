%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.orvonbwlBA

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:11 EST 2020

% Result     : Theorem 0.94s
% Output     : Refutation 0.94s
% Verified   : 
% Statistics : Number of formulae       :  179 (3028 expanded)
%              Number of leaves         :   35 ( 876 expanded)
%              Depth                    :   34
%              Number of atoms          : 1346 (41775 expanded)
%              Number of equality atoms :  125 (2623 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['2','3'])).

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
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['23','26'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['18','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('33',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X22 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','37'])).

thf('39',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['18','29'])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('50',plain,
    ( ( v4_relat_1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('51',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v4_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('52',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('54',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('55',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X22 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('60',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
        | ~ ( v1_relat_1 @ sk_D )
        | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
        | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('62',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('63',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
        | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','63'])).

thf('65',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('68',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('69',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','44','66','67','68'])).

thf('70',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','69'])).

thf('71',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('72',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','37'])).

thf('73',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('74',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['74','79'])).

thf('81',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('83',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('84',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('86',plain,
    ( ( ( k1_relat_1 @ sk_D )
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ ( k1_relat_1 @ sk_D ) )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['81','87'])).

thf('89',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('90',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('91',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('92',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','44','66','67','68'])).

thf('94',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['92','93'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','63'])).

thf('96',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ X0 @ sk_C @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ X0 @ sk_C @ sk_D )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ X0 )
        | ( v1_funct_2 @ sk_D @ X0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
      | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('104',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['74','79'])).

thf('105',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
      | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('107',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('109',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['23','26'])).

thf('111',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('112',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ sk_D ) )
      | ( sk_B
        = ( k2_relat_1 @ sk_D ) ) )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('115',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('116',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_D ) )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','44','66','67','68'])).

thf('118',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('120',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
        | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) )
        | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('122',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('123',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('124',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['120','121','122','123'])).

thf('125',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('126',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
        | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('128',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['126','128'])).

thf('130',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['102','129'])).

thf('131',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['94','130'])).

thf('132',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('133',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['131','132'])).

thf('134',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['89','133'])).

thf('135',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['88','134'])).

thf('136',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['80','135'])).

thf('137',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['89','133'])).

thf('138',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','138'])).

thf('140',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['89','133'])).

thf('141',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['139','140'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['70','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.orvonbwlBA
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:09:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.94/1.15  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.94/1.15  % Solved by: fo/fo7.sh
% 0.94/1.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.94/1.15  % done 749 iterations in 0.682s
% 0.94/1.15  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.94/1.15  % SZS output start Refutation
% 0.94/1.15  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.94/1.15  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.94/1.15  thf(sk_B_type, type, sk_B: $i).
% 0.94/1.15  thf(sk_D_type, type, sk_D: $i).
% 0.94/1.15  thf(sk_A_type, type, sk_A: $i).
% 0.94/1.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.94/1.15  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.94/1.15  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.94/1.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.94/1.15  thf(sk_C_type, type, sk_C: $i).
% 0.94/1.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.94/1.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.94/1.15  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.94/1.15  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.94/1.15  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.94/1.15  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.94/1.15  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.94/1.15  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.94/1.15  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.94/1.15  thf(t9_funct_2, conjecture,
% 0.94/1.15    (![A:$i,B:$i,C:$i,D:$i]:
% 0.94/1.15     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.94/1.15         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.94/1.15       ( ( r1_tarski @ B @ C ) =>
% 0.94/1.15         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.94/1.15           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.94/1.15             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.94/1.15  thf(zf_stmt_0, negated_conjecture,
% 0.94/1.15    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.94/1.15        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.94/1.15            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.94/1.15          ( ( r1_tarski @ B @ C ) =>
% 0.94/1.15            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.94/1.15              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.94/1.15                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.94/1.15    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.94/1.15  thf('0', plain,
% 0.94/1.15      ((~ (v1_funct_1 @ sk_D)
% 0.94/1.15        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.94/1.15        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('1', plain,
% 0.94/1.15      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.94/1.15         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.94/1.15      inference('split', [status(esa)], ['0'])).
% 0.94/1.15  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.94/1.15      inference('split', [status(esa)], ['0'])).
% 0.94/1.15  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.94/1.15      inference('sup-', [status(thm)], ['2', '3'])).
% 0.94/1.15  thf(d1_funct_2, axiom,
% 0.94/1.15    (![A:$i,B:$i,C:$i]:
% 0.94/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.94/1.15       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.94/1.15           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.94/1.15             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.94/1.15         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.94/1.15           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.94/1.15             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.94/1.15  thf(zf_stmt_1, axiom,
% 0.94/1.15    (![B:$i,A:$i]:
% 0.94/1.15     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.94/1.15       ( zip_tseitin_0 @ B @ A ) ))).
% 0.94/1.15  thf('5', plain,
% 0.94/1.15      (![X23 : $i, X24 : $i]:
% 0.94/1.15         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.94/1.15  thf('6', plain,
% 0.94/1.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.94/1.15  thf(zf_stmt_3, axiom,
% 0.94/1.15    (![C:$i,B:$i,A:$i]:
% 0.94/1.15     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.94/1.15       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.94/1.15  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.94/1.15  thf(zf_stmt_5, axiom,
% 0.94/1.15    (![A:$i,B:$i,C:$i]:
% 0.94/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.94/1.15       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.94/1.15         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.94/1.15           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.94/1.15             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.94/1.15  thf('7', plain,
% 0.94/1.15      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.94/1.15         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.94/1.15          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.94/1.15          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.94/1.15  thf('8', plain,
% 0.94/1.15      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.94/1.15      inference('sup-', [status(thm)], ['6', '7'])).
% 0.94/1.15  thf('9', plain,
% 0.94/1.15      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.94/1.15      inference('sup-', [status(thm)], ['5', '8'])).
% 0.94/1.15  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('11', plain,
% 0.94/1.15      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.94/1.15         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.94/1.15          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.94/1.15          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.94/1.15  thf('12', plain,
% 0.94/1.15      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.94/1.15        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['10', '11'])).
% 0.94/1.15  thf('13', plain,
% 0.94/1.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf(redefinition_k1_relset_1, axiom,
% 0.94/1.15    (![A:$i,B:$i,C:$i]:
% 0.94/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.94/1.15       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.94/1.15  thf('14', plain,
% 0.94/1.15      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.94/1.15         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.94/1.15          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.94/1.15      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.94/1.15  thf('15', plain,
% 0.94/1.15      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.94/1.15      inference('sup-', [status(thm)], ['13', '14'])).
% 0.94/1.15  thf('16', plain,
% 0.94/1.15      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.94/1.15      inference('demod', [status(thm)], ['12', '15'])).
% 0.94/1.15  thf('17', plain,
% 0.94/1.15      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['9', '16'])).
% 0.94/1.15  thf('18', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('19', plain,
% 0.94/1.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf(cc2_relset_1, axiom,
% 0.94/1.15    (![A:$i,B:$i,C:$i]:
% 0.94/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.94/1.15       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.94/1.15  thf('20', plain,
% 0.94/1.15      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.94/1.15         ((v5_relat_1 @ X14 @ X16)
% 0.94/1.15          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.94/1.15      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.94/1.15  thf('21', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.94/1.15      inference('sup-', [status(thm)], ['19', '20'])).
% 0.94/1.15  thf(d19_relat_1, axiom,
% 0.94/1.15    (![A:$i,B:$i]:
% 0.94/1.15     ( ( v1_relat_1 @ B ) =>
% 0.94/1.15       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.94/1.15  thf('22', plain,
% 0.94/1.15      (![X9 : $i, X10 : $i]:
% 0.94/1.15         (~ (v5_relat_1 @ X9 @ X10)
% 0.94/1.15          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.94/1.15          | ~ (v1_relat_1 @ X9))),
% 0.94/1.15      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.94/1.15  thf('23', plain,
% 0.94/1.15      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.94/1.15      inference('sup-', [status(thm)], ['21', '22'])).
% 0.94/1.15  thf('24', plain,
% 0.94/1.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf(cc1_relset_1, axiom,
% 0.94/1.15    (![A:$i,B:$i,C:$i]:
% 0.94/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.94/1.15       ( v1_relat_1 @ C ) ))).
% 0.94/1.15  thf('25', plain,
% 0.94/1.15      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.94/1.15         ((v1_relat_1 @ X11)
% 0.94/1.15          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.94/1.15      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.94/1.15  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.94/1.15      inference('sup-', [status(thm)], ['24', '25'])).
% 0.94/1.15  thf('27', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.94/1.15      inference('demod', [status(thm)], ['23', '26'])).
% 0.94/1.15  thf(t1_xboole_1, axiom,
% 0.94/1.15    (![A:$i,B:$i,C:$i]:
% 0.94/1.15     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.94/1.15       ( r1_tarski @ A @ C ) ))).
% 0.94/1.15  thf('28', plain,
% 0.94/1.15      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.94/1.15         (~ (r1_tarski @ X3 @ X4)
% 0.94/1.15          | ~ (r1_tarski @ X4 @ X5)
% 0.94/1.15          | (r1_tarski @ X3 @ X5))),
% 0.94/1.15      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.94/1.15  thf('29', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.94/1.15      inference('sup-', [status(thm)], ['27', '28'])).
% 0.94/1.15  thf('30', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.94/1.15      inference('sup-', [status(thm)], ['18', '29'])).
% 0.94/1.15  thf(d10_xboole_0, axiom,
% 0.94/1.15    (![A:$i,B:$i]:
% 0.94/1.15     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.94/1.15  thf('31', plain,
% 0.94/1.15      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.94/1.15      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.94/1.15  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.94/1.15      inference('simplify', [status(thm)], ['31'])).
% 0.94/1.15  thf(t11_relset_1, axiom,
% 0.94/1.15    (![A:$i,B:$i,C:$i]:
% 0.94/1.15     ( ( v1_relat_1 @ C ) =>
% 0.94/1.15       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.94/1.15           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.94/1.15         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.94/1.15  thf('33', plain,
% 0.94/1.15      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.94/1.15         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.94/1.15          | ~ (r1_tarski @ (k2_relat_1 @ X20) @ X22)
% 0.94/1.15          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.94/1.15          | ~ (v1_relat_1 @ X20))),
% 0.94/1.15      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.94/1.15  thf('34', plain,
% 0.94/1.15      (![X0 : $i, X1 : $i]:
% 0.94/1.15         (~ (v1_relat_1 @ X0)
% 0.94/1.15          | (m1_subset_1 @ X0 @ 
% 0.94/1.15             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.94/1.15          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.94/1.15      inference('sup-', [status(thm)], ['32', '33'])).
% 0.94/1.15  thf('35', plain,
% 0.94/1.15      (((m1_subset_1 @ sk_D @ 
% 0.94/1.15         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))
% 0.94/1.15        | ~ (v1_relat_1 @ sk_D))),
% 0.94/1.15      inference('sup-', [status(thm)], ['30', '34'])).
% 0.94/1.15  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 0.94/1.15      inference('sup-', [status(thm)], ['24', '25'])).
% 0.94/1.15  thf('37', plain,
% 0.94/1.15      ((m1_subset_1 @ sk_D @ 
% 0.94/1.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 0.94/1.15      inference('demod', [status(thm)], ['35', '36'])).
% 0.94/1.15  thf('38', plain,
% 0.94/1.15      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.94/1.15        | ((sk_B) = (k1_xboole_0)))),
% 0.94/1.15      inference('sup+', [status(thm)], ['17', '37'])).
% 0.94/1.15  thf('39', plain,
% 0.94/1.15      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.94/1.15         <= (~
% 0.94/1.15             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.94/1.15      inference('split', [status(esa)], ['0'])).
% 0.94/1.15  thf('40', plain,
% 0.94/1.15      ((((sk_B) = (k1_xboole_0)))
% 0.94/1.15         <= (~
% 0.94/1.15             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['38', '39'])).
% 0.94/1.15  thf('41', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('42', plain,
% 0.94/1.15      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.94/1.15      inference('split', [status(esa)], ['41'])).
% 0.94/1.15  thf('43', plain,
% 0.94/1.15      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.94/1.15         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.94/1.15             ~
% 0.94/1.15             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['40', '42'])).
% 0.94/1.15  thf('44', plain,
% 0.94/1.15      ((((sk_B) = (k1_xboole_0))) | 
% 0.94/1.15       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.94/1.15      inference('simplify', [status(thm)], ['43'])).
% 0.94/1.15  thf('45', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.94/1.15      inference('sup-', [status(thm)], ['18', '29'])).
% 0.94/1.15  thf('46', plain,
% 0.94/1.15      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('split', [status(esa)], ['41'])).
% 0.94/1.15  thf('47', plain,
% 0.94/1.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('48', plain,
% 0.94/1.15      (((m1_subset_1 @ sk_D @ 
% 0.94/1.15         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup+', [status(thm)], ['46', '47'])).
% 0.94/1.15  thf('49', plain,
% 0.94/1.15      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.94/1.15         ((v4_relat_1 @ X14 @ X15)
% 0.94/1.15          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.94/1.15      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.94/1.15  thf('50', plain,
% 0.94/1.15      (((v4_relat_1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['48', '49'])).
% 0.94/1.15  thf(d18_relat_1, axiom,
% 0.94/1.15    (![A:$i,B:$i]:
% 0.94/1.15     ( ( v1_relat_1 @ B ) =>
% 0.94/1.15       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.94/1.15  thf('51', plain,
% 0.94/1.15      (![X7 : $i, X8 : $i]:
% 0.94/1.15         (~ (v4_relat_1 @ X7 @ X8)
% 0.94/1.15          | (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.94/1.15          | ~ (v1_relat_1 @ X7))),
% 0.94/1.15      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.94/1.15  thf('52', plain,
% 0.94/1.15      (((~ (v1_relat_1 @ sk_D)
% 0.94/1.15         | (r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0)))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['50', '51'])).
% 0.94/1.15  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 0.94/1.15      inference('sup-', [status(thm)], ['24', '25'])).
% 0.94/1.15  thf('54', plain,
% 0.94/1.15      (((r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('demod', [status(thm)], ['52', '53'])).
% 0.94/1.15  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.94/1.15  thf('55', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.94/1.15      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.94/1.15  thf('56', plain,
% 0.94/1.15      (![X0 : $i, X2 : $i]:
% 0.94/1.15         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.94/1.15      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.94/1.15  thf('57', plain,
% 0.94/1.15      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['55', '56'])).
% 0.94/1.15  thf('58', plain,
% 0.94/1.15      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['54', '57'])).
% 0.94/1.15  thf('59', plain,
% 0.94/1.15      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.94/1.15         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.94/1.15          | ~ (r1_tarski @ (k2_relat_1 @ X20) @ X22)
% 0.94/1.15          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.94/1.15          | ~ (v1_relat_1 @ X20))),
% 0.94/1.15      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.94/1.15  thf('60', plain,
% 0.94/1.15      ((![X0 : $i, X1 : $i]:
% 0.94/1.15          (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.94/1.15           | ~ (v1_relat_1 @ sk_D)
% 0.94/1.15           | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.94/1.15           | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X1)))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['58', '59'])).
% 0.94/1.15  thf('61', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.94/1.15      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.94/1.15  thf('62', plain, ((v1_relat_1 @ sk_D)),
% 0.94/1.15      inference('sup-', [status(thm)], ['24', '25'])).
% 0.94/1.15  thf('63', plain,
% 0.94/1.15      ((![X0 : $i, X1 : $i]:
% 0.94/1.15          ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.94/1.15           | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X1)))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.94/1.15  thf('64', plain,
% 0.94/1.15      ((![X0 : $i]:
% 0.94/1.15          (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C))))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['45', '63'])).
% 0.94/1.15  thf('65', plain,
% 0.94/1.15      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.94/1.15         <= (~
% 0.94/1.15             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.94/1.15      inference('split', [status(esa)], ['0'])).
% 0.94/1.15  thf('66', plain,
% 0.94/1.15      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.94/1.15       ~ (((sk_A) = (k1_xboole_0)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['64', '65'])).
% 0.94/1.15  thf('67', plain, ((((sk_A) = (k1_xboole_0))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.94/1.15      inference('split', [status(esa)], ['41'])).
% 0.94/1.15  thf('68', plain,
% 0.94/1.15      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.94/1.15       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.94/1.15       ~ ((v1_funct_1 @ sk_D))),
% 0.94/1.15      inference('split', [status(esa)], ['0'])).
% 0.94/1.15  thf('69', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.94/1.15      inference('sat_resolution*', [status(thm)], ['4', '44', '66', '67', '68'])).
% 0.94/1.15  thf('70', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.94/1.15      inference('simpl_trail', [status(thm)], ['1', '69'])).
% 0.94/1.15  thf('71', plain,
% 0.94/1.15      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['9', '16'])).
% 0.94/1.15  thf('72', plain,
% 0.94/1.15      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.94/1.15        | ((sk_B) = (k1_xboole_0)))),
% 0.94/1.15      inference('sup+', [status(thm)], ['17', '37'])).
% 0.94/1.15  thf('73', plain,
% 0.94/1.15      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.94/1.15         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.94/1.15          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.94/1.15          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.94/1.15  thf('74', plain,
% 0.94/1.15      ((((sk_B) = (k1_xboole_0))
% 0.94/1.15        | (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.94/1.15        | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.94/1.15      inference('sup-', [status(thm)], ['72', '73'])).
% 0.94/1.15  thf('75', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('76', plain,
% 0.94/1.15      (![X23 : $i, X24 : $i]:
% 0.94/1.15         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.94/1.15  thf('77', plain,
% 0.94/1.15      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['55', '56'])).
% 0.94/1.15  thf('78', plain,
% 0.94/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.94/1.15         (~ (r1_tarski @ X1 @ X0)
% 0.94/1.15          | (zip_tseitin_0 @ X0 @ X2)
% 0.94/1.15          | ((X1) = (k1_xboole_0)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['76', '77'])).
% 0.94/1.15  thf('79', plain,
% 0.94/1.15      (![X0 : $i]: (((sk_B) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_C @ X0))),
% 0.94/1.15      inference('sup-', [status(thm)], ['75', '78'])).
% 0.94/1.15  thf('80', plain,
% 0.94/1.15      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.94/1.15      inference('clc', [status(thm)], ['74', '79'])).
% 0.94/1.15  thf('81', plain,
% 0.94/1.15      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['9', '16'])).
% 0.94/1.15  thf('82', plain,
% 0.94/1.15      ((m1_subset_1 @ sk_D @ 
% 0.94/1.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 0.94/1.15      inference('demod', [status(thm)], ['35', '36'])).
% 0.94/1.15  thf('83', plain,
% 0.94/1.15      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.94/1.15         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.94/1.15          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.94/1.15      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.94/1.15  thf('84', plain,
% 0.94/1.15      (((k1_relset_1 @ (k1_relat_1 @ sk_D) @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.94/1.15      inference('sup-', [status(thm)], ['82', '83'])).
% 0.94/1.15  thf('85', plain,
% 0.94/1.15      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.94/1.15         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 0.94/1.15          | (v1_funct_2 @ X27 @ X25 @ X26)
% 0.94/1.15          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.94/1.15  thf('86', plain,
% 0.94/1.15      ((((k1_relat_1 @ sk_D) != (k1_relat_1 @ sk_D))
% 0.94/1.15        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ (k1_relat_1 @ sk_D))
% 0.94/1.15        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C))),
% 0.94/1.15      inference('sup-', [status(thm)], ['84', '85'])).
% 0.94/1.15  thf('87', plain,
% 0.94/1.15      (((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C)
% 0.94/1.15        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ (k1_relat_1 @ sk_D)))),
% 0.94/1.15      inference('simplify', [status(thm)], ['86'])).
% 0.94/1.15  thf('88', plain,
% 0.94/1.15      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.94/1.15        | ((sk_B) = (k1_xboole_0))
% 0.94/1.15        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C))),
% 0.94/1.15      inference('sup-', [status(thm)], ['81', '87'])).
% 0.94/1.15  thf('89', plain,
% 0.94/1.15      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.94/1.15      inference('split', [status(esa)], ['41'])).
% 0.94/1.15  thf('90', plain,
% 0.94/1.15      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('split', [status(esa)], ['41'])).
% 0.94/1.15  thf('91', plain,
% 0.94/1.15      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.94/1.15         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.94/1.15      inference('split', [status(esa)], ['0'])).
% 0.94/1.15  thf('92', plain,
% 0.94/1.15      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.94/1.15         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['90', '91'])).
% 0.94/1.15  thf('93', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.94/1.15      inference('sat_resolution*', [status(thm)], ['4', '44', '66', '67', '68'])).
% 0.94/1.15  thf('94', plain,
% 0.94/1.15      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('simpl_trail', [status(thm)], ['92', '93'])).
% 0.94/1.15  thf('95', plain,
% 0.94/1.15      ((![X0 : $i]:
% 0.94/1.15          (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C))))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['45', '63'])).
% 0.94/1.15  thf('96', plain,
% 0.94/1.15      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.94/1.15         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.94/1.15          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.94/1.15      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.94/1.15  thf('97', plain,
% 0.94/1.15      ((![X0 : $i]: ((k1_relset_1 @ X0 @ sk_C @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['95', '96'])).
% 0.94/1.15  thf('98', plain,
% 0.94/1.15      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['54', '57'])).
% 0.94/1.15  thf('99', plain,
% 0.94/1.15      ((![X0 : $i]: ((k1_relset_1 @ X0 @ sk_C @ sk_D) = (k1_xboole_0)))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('demod', [status(thm)], ['97', '98'])).
% 0.94/1.15  thf('100', plain,
% 0.94/1.15      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.94/1.15         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 0.94/1.15          | (v1_funct_2 @ X27 @ X25 @ X26)
% 0.94/1.15          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.94/1.15  thf('101', plain,
% 0.94/1.15      ((![X0 : $i]:
% 0.94/1.15          (((X0) != (k1_xboole_0))
% 0.94/1.15           | ~ (zip_tseitin_1 @ sk_D @ sk_C @ X0)
% 0.94/1.15           | (v1_funct_2 @ sk_D @ X0 @ sk_C)))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['99', '100'])).
% 0.94/1.15  thf('102', plain,
% 0.94/1.15      ((((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C)
% 0.94/1.15         | ~ (zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0)))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('simplify', [status(thm)], ['101'])).
% 0.94/1.15  thf('103', plain,
% 0.94/1.15      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('split', [status(esa)], ['41'])).
% 0.94/1.15  thf('104', plain,
% 0.94/1.15      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.94/1.15      inference('clc', [status(thm)], ['74', '79'])).
% 0.94/1.15  thf('105', plain,
% 0.94/1.15      ((((zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0) | ((sk_B) = (k1_xboole_0))))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup+', [status(thm)], ['103', '104'])).
% 0.94/1.15  thf('106', plain,
% 0.94/1.15      ((((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C)
% 0.94/1.15         | ~ (zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0)))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('simplify', [status(thm)], ['101'])).
% 0.94/1.15  thf('107', plain,
% 0.94/1.15      (((((sk_B) = (k1_xboole_0)) | (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C)))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['105', '106'])).
% 0.94/1.15  thf('108', plain,
% 0.94/1.15      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.94/1.15         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['90', '91'])).
% 0.94/1.15  thf('109', plain,
% 0.94/1.15      ((((sk_B) = (k1_xboole_0)))
% 0.94/1.15         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['107', '108'])).
% 0.94/1.15  thf('110', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.94/1.15      inference('demod', [status(thm)], ['23', '26'])).
% 0.94/1.15  thf('111', plain,
% 0.94/1.15      (![X0 : $i, X2 : $i]:
% 0.94/1.15         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.94/1.15      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.94/1.15  thf('112', plain,
% 0.94/1.15      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))
% 0.94/1.15        | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['110', '111'])).
% 0.94/1.15  thf('113', plain,
% 0.94/1.15      (((~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ sk_D))
% 0.94/1.15         | ((sk_B) = (k2_relat_1 @ sk_D))))
% 0.94/1.15         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['109', '112'])).
% 0.94/1.15  thf('114', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.94/1.15      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.94/1.15  thf('115', plain,
% 0.94/1.15      ((((sk_B) = (k1_xboole_0)))
% 0.94/1.15         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['107', '108'])).
% 0.94/1.15  thf('116', plain,
% 0.94/1.15      ((((k1_xboole_0) = (k2_relat_1 @ sk_D)))
% 0.94/1.15         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.94/1.15  thf('117', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.94/1.15      inference('sat_resolution*', [status(thm)], ['4', '44', '66', '67', '68'])).
% 0.94/1.15  thf('118', plain,
% 0.94/1.15      ((((k1_xboole_0) = (k2_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('simpl_trail', [status(thm)], ['116', '117'])).
% 0.94/1.15  thf('119', plain,
% 0.94/1.15      (![X0 : $i, X1 : $i]:
% 0.94/1.15         (~ (v1_relat_1 @ X0)
% 0.94/1.15          | (m1_subset_1 @ X0 @ 
% 0.94/1.15             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.94/1.15          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.94/1.15      inference('sup-', [status(thm)], ['32', '33'])).
% 0.94/1.15  thf('120', plain,
% 0.94/1.15      ((![X0 : $i]:
% 0.94/1.15          (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.94/1.15           | (m1_subset_1 @ sk_D @ 
% 0.94/1.15              (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)))
% 0.94/1.15           | ~ (v1_relat_1 @ sk_D)))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['118', '119'])).
% 0.94/1.15  thf('121', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.94/1.15      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.94/1.15  thf('122', plain,
% 0.94/1.15      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['54', '57'])).
% 0.94/1.15  thf('123', plain, ((v1_relat_1 @ sk_D)),
% 0.94/1.15      inference('sup-', [status(thm)], ['24', '25'])).
% 0.94/1.15  thf('124', plain,
% 0.94/1.15      ((![X0 : $i]:
% 0.94/1.15          (m1_subset_1 @ sk_D @ 
% 0.94/1.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0))))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('demod', [status(thm)], ['120', '121', '122', '123'])).
% 0.94/1.15  thf('125', plain,
% 0.94/1.15      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.94/1.15         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.94/1.15          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.94/1.15          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.94/1.15  thf('126', plain,
% 0.94/1.15      ((![X0 : $i]:
% 0.94/1.15          ((zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0)
% 0.94/1.15           | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0)))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('sup-', [status(thm)], ['124', '125'])).
% 0.94/1.15  thf('127', plain,
% 0.94/1.15      (![X23 : $i, X24 : $i]:
% 0.94/1.15         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.94/1.15  thf('128', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 0.94/1.15      inference('simplify', [status(thm)], ['127'])).
% 0.94/1.15  thf('129', plain,
% 0.94/1.15      ((![X0 : $i]: (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('demod', [status(thm)], ['126', '128'])).
% 0.94/1.15  thf('130', plain,
% 0.94/1.15      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.94/1.15         <= ((((sk_A) = (k1_xboole_0))))),
% 0.94/1.15      inference('demod', [status(thm)], ['102', '129'])).
% 0.94/1.15  thf('131', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.94/1.15      inference('demod', [status(thm)], ['94', '130'])).
% 0.94/1.15  thf('132', plain,
% 0.94/1.15      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.94/1.15      inference('split', [status(esa)], ['41'])).
% 0.94/1.15  thf('133', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.94/1.15      inference('sat_resolution*', [status(thm)], ['131', '132'])).
% 0.94/1.15  thf('134', plain, (((sk_B) != (k1_xboole_0))),
% 0.94/1.15      inference('simpl_trail', [status(thm)], ['89', '133'])).
% 0.94/1.15  thf('135', plain,
% 0.94/1.15      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.94/1.15        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C))),
% 0.94/1.15      inference('simplify_reflect-', [status(thm)], ['88', '134'])).
% 0.94/1.15  thf('136', plain,
% 0.94/1.15      ((((sk_B) = (k1_xboole_0))
% 0.94/1.15        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C))),
% 0.94/1.15      inference('sup-', [status(thm)], ['80', '135'])).
% 0.94/1.15  thf('137', plain, (((sk_B) != (k1_xboole_0))),
% 0.94/1.15      inference('simpl_trail', [status(thm)], ['89', '133'])).
% 0.94/1.15  thf('138', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.94/1.15      inference('simplify_reflect-', [status(thm)], ['136', '137'])).
% 0.94/1.15  thf('139', plain,
% 0.94/1.15      (((v1_funct_2 @ sk_D @ sk_A @ sk_C) | ((sk_B) = (k1_xboole_0)))),
% 0.94/1.15      inference('sup+', [status(thm)], ['71', '138'])).
% 0.94/1.15  thf('140', plain, (((sk_B) != (k1_xboole_0))),
% 0.94/1.15      inference('simpl_trail', [status(thm)], ['89', '133'])).
% 0.94/1.15  thf('141', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.94/1.15      inference('simplify_reflect-', [status(thm)], ['139', '140'])).
% 0.94/1.15  thf('142', plain, ($false), inference('demod', [status(thm)], ['70', '141'])).
% 0.94/1.15  
% 0.94/1.15  % SZS output end Refutation
% 0.94/1.15  
% 1.02/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
