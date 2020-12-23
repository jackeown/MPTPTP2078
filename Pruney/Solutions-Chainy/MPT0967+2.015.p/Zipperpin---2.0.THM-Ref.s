%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.slsnDqDSGj

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:13 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 534 expanded)
%              Number of leaves         :   33 ( 161 expanded)
%              Depth                    :   18
%              Number of atoms          :  921 (8040 expanded)
%              Number of equality atoms :   76 ( 521 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ( v1_funct_2 @ X29 @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','35'])).

thf('37',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('44',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('47',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('52',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('55',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X22 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,(
    ! [X21: $i] :
      ( zip_tseitin_0 @ X21 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','58'])).

thf('60',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','59'])).

thf('61',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('62',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('64',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('68',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('69',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['4','42','66','67','68'])).

thf('70',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','69'])).

thf('71',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('72',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['18','29'])).

thf('73',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X29 ) @ X30 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('76',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('78',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('79',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','79'])).

thf('81',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('82',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','59'])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('84',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('86',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','42','66','68','88','67'])).

thf('90',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['81','89'])).

thf('91',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['80','90'])).

thf('92',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('93',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['70','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.slsnDqDSGj
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:00:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.69/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.88  % Solved by: fo/fo7.sh
% 0.69/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.88  % done 613 iterations in 0.390s
% 0.69/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.88  % SZS output start Refutation
% 0.69/0.88  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.69/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.88  thf(sk_D_type, type, sk_D: $i).
% 0.69/0.88  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.88  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.69/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.88  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.69/0.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.69/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.69/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.69/0.88  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.69/0.88  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.69/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.69/0.88  thf(t9_funct_2, conjecture,
% 0.69/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.88     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.69/0.88         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.88       ( ( r1_tarski @ B @ C ) =>
% 0.69/0.88         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.69/0.88           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.69/0.88             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.69/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.88    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.88        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.69/0.88            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.88          ( ( r1_tarski @ B @ C ) =>
% 0.69/0.88            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.69/0.88              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.69/0.88                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.69/0.88    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.69/0.88  thf('0', plain,
% 0.69/0.88      ((~ (v1_funct_1 @ sk_D)
% 0.69/0.88        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.69/0.88        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('1', plain,
% 0.69/0.88      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.69/0.88         <= (~
% 0.69/0.88             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.69/0.88      inference('split', [status(esa)], ['0'])).
% 0.69/0.88  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.69/0.88      inference('split', [status(esa)], ['0'])).
% 0.69/0.88  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.69/0.88      inference('sup-', [status(thm)], ['2', '3'])).
% 0.69/0.88  thf(d1_funct_2, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.69/0.88           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.69/0.88             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.69/0.88         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.69/0.88           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.69/0.88             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.69/0.88  thf(zf_stmt_1, axiom,
% 0.69/0.88    (![B:$i,A:$i]:
% 0.69/0.88     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.69/0.88       ( zip_tseitin_0 @ B @ A ) ))).
% 0.69/0.88  thf('5', plain,
% 0.69/0.88      (![X21 : $i, X22 : $i]:
% 0.69/0.88         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.69/0.88  thf('6', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.69/0.88  thf(zf_stmt_3, axiom,
% 0.69/0.88    (![C:$i,B:$i,A:$i]:
% 0.69/0.88     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.69/0.88       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.69/0.88  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.69/0.88  thf(zf_stmt_5, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.69/0.88         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.69/0.88           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.69/0.88             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.69/0.88  thf('7', plain,
% 0.69/0.88      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.69/0.88         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.69/0.88          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.69/0.88          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.69/0.88  thf('8', plain,
% 0.69/0.88      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.69/0.88      inference('sup-', [status(thm)], ['6', '7'])).
% 0.69/0.88  thf('9', plain,
% 0.69/0.88      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.69/0.88      inference('sup-', [status(thm)], ['5', '8'])).
% 0.69/0.88  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('11', plain,
% 0.69/0.88      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.69/0.88         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.69/0.88          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.69/0.88          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.69/0.88  thf('12', plain,
% 0.69/0.88      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.69/0.88        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['10', '11'])).
% 0.69/0.88  thf('13', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(redefinition_k1_relset_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.69/0.88  thf('14', plain,
% 0.69/0.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.69/0.88         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.69/0.88          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.69/0.88  thf('15', plain,
% 0.69/0.88      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.69/0.88      inference('sup-', [status(thm)], ['13', '14'])).
% 0.69/0.88  thf('16', plain,
% 0.69/0.88      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.69/0.88      inference('demod', [status(thm)], ['12', '15'])).
% 0.69/0.88  thf('17', plain,
% 0.69/0.88      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['9', '16'])).
% 0.69/0.88  thf('18', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('19', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(cc2_relset_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.69/0.88  thf('20', plain,
% 0.69/0.88      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.69/0.88         ((v5_relat_1 @ X15 @ X17)
% 0.69/0.88          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.69/0.88      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.69/0.88  thf('21', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.69/0.88      inference('sup-', [status(thm)], ['19', '20'])).
% 0.69/0.88  thf(d19_relat_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( v1_relat_1 @ B ) =>
% 0.69/0.88       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.69/0.88  thf('22', plain,
% 0.69/0.88      (![X10 : $i, X11 : $i]:
% 0.69/0.88         (~ (v5_relat_1 @ X10 @ X11)
% 0.69/0.88          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.69/0.88          | ~ (v1_relat_1 @ X10))),
% 0.69/0.88      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.69/0.88  thf('23', plain,
% 0.69/0.88      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.69/0.88      inference('sup-', [status(thm)], ['21', '22'])).
% 0.69/0.88  thf('24', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(cc1_relset_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( v1_relat_1 @ C ) ))).
% 0.69/0.88  thf('25', plain,
% 0.69/0.88      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.69/0.88         ((v1_relat_1 @ X12)
% 0.69/0.88          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.69/0.88      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.69/0.88  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.69/0.88      inference('sup-', [status(thm)], ['24', '25'])).
% 0.69/0.88  thf('27', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.69/0.88      inference('demod', [status(thm)], ['23', '26'])).
% 0.69/0.88  thf(t1_xboole_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.69/0.88       ( r1_tarski @ A @ C ) ))).
% 0.69/0.88  thf('28', plain,
% 0.69/0.88      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.69/0.88         (~ (r1_tarski @ X3 @ X4)
% 0.69/0.88          | ~ (r1_tarski @ X4 @ X5)
% 0.69/0.88          | (r1_tarski @ X3 @ X5))),
% 0.69/0.88      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.69/0.88  thf('29', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['27', '28'])).
% 0.69/0.88  thf('30', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.69/0.88      inference('sup-', [status(thm)], ['18', '29'])).
% 0.69/0.88  thf(t4_funct_2, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.69/0.88       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.69/0.88         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.69/0.88           ( m1_subset_1 @
% 0.69/0.88             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.69/0.88  thf('31', plain,
% 0.69/0.88      (![X29 : $i, X30 : $i]:
% 0.69/0.88         (~ (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 0.69/0.88          | (v1_funct_2 @ X29 @ (k1_relat_1 @ X29) @ X30)
% 0.69/0.88          | ~ (v1_funct_1 @ X29)
% 0.69/0.88          | ~ (v1_relat_1 @ X29))),
% 0.69/0.88      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.69/0.88  thf('32', plain,
% 0.69/0.88      ((~ (v1_relat_1 @ sk_D)
% 0.69/0.88        | ~ (v1_funct_1 @ sk_D)
% 0.69/0.88        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C))),
% 0.69/0.88      inference('sup-', [status(thm)], ['30', '31'])).
% 0.69/0.88  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 0.69/0.88      inference('sup-', [status(thm)], ['24', '25'])).
% 0.69/0.88  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('35', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.69/0.88      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.69/0.88  thf('36', plain,
% 0.69/0.88      (((v1_funct_2 @ sk_D @ sk_A @ sk_C) | ((sk_B) = (k1_xboole_0)))),
% 0.69/0.88      inference('sup+', [status(thm)], ['17', '35'])).
% 0.69/0.88  thf('37', plain,
% 0.69/0.88      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.69/0.88         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.69/0.88      inference('split', [status(esa)], ['0'])).
% 0.69/0.88  thf('38', plain,
% 0.69/0.88      ((((sk_B) = (k1_xboole_0))) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['36', '37'])).
% 0.69/0.88  thf('39', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('40', plain,
% 0.69/0.88      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.69/0.88      inference('split', [status(esa)], ['39'])).
% 0.69/0.88  thf('41', plain,
% 0.69/0.88      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.69/0.88         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.69/0.88             ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['38', '40'])).
% 0.69/0.88  thf('42', plain,
% 0.69/0.88      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | (((sk_B) = (k1_xboole_0)))),
% 0.69/0.88      inference('simplify', [status(thm)], ['41'])).
% 0.69/0.88  thf('43', plain,
% 0.69/0.88      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('split', [status(esa)], ['39'])).
% 0.69/0.88  thf('44', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('45', plain,
% 0.69/0.88      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.69/0.88         <= ((((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup+', [status(thm)], ['43', '44'])).
% 0.69/0.88  thf('46', plain,
% 0.69/0.88      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.69/0.88         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.69/0.88          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.69/0.88          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.69/0.88  thf('47', plain,
% 0.69/0.88      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.69/0.88         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 0.69/0.88         <= ((((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['45', '46'])).
% 0.69/0.88  thf('48', plain,
% 0.69/0.88      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('split', [status(esa)], ['39'])).
% 0.69/0.88  thf('49', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('50', plain,
% 0.69/0.88      (((m1_subset_1 @ sk_D @ 
% 0.69/0.88         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.69/0.88         <= ((((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup+', [status(thm)], ['48', '49'])).
% 0.69/0.88  thf('51', plain,
% 0.69/0.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.69/0.88         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.69/0.88          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.69/0.88  thf('52', plain,
% 0.69/0.88      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.69/0.88         <= ((((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['50', '51'])).
% 0.69/0.88  thf('53', plain,
% 0.69/0.88      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.69/0.88         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 0.69/0.88         <= ((((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('demod', [status(thm)], ['47', '52'])).
% 0.69/0.88  thf('54', plain,
% 0.69/0.88      (((m1_subset_1 @ sk_D @ 
% 0.69/0.88         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.69/0.88         <= ((((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup+', [status(thm)], ['48', '49'])).
% 0.69/0.88  thf('55', plain,
% 0.69/0.88      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.69/0.88         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.69/0.88          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.69/0.88          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.69/0.88  thf('56', plain,
% 0.69/0.88      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.69/0.88         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.69/0.88         <= ((((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['54', '55'])).
% 0.69/0.88  thf('57', plain,
% 0.69/0.88      (![X21 : $i, X22 : $i]:
% 0.69/0.88         ((zip_tseitin_0 @ X21 @ X22) | ((X22) != (k1_xboole_0)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.69/0.88  thf('58', plain, (![X21 : $i]: (zip_tseitin_0 @ X21 @ k1_xboole_0)),
% 0.69/0.88      inference('simplify', [status(thm)], ['57'])).
% 0.69/0.88  thf('59', plain,
% 0.69/0.88      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 0.69/0.88         <= ((((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('demod', [status(thm)], ['56', '58'])).
% 0.69/0.88  thf('60', plain,
% 0.69/0.88      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('demod', [status(thm)], ['53', '59'])).
% 0.69/0.88  thf('61', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.69/0.88      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.69/0.88  thf('62', plain,
% 0.69/0.88      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.69/0.88         <= ((((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup+', [status(thm)], ['60', '61'])).
% 0.69/0.88  thf('63', plain,
% 0.69/0.88      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('split', [status(esa)], ['39'])).
% 0.69/0.88  thf('64', plain,
% 0.69/0.88      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.69/0.88         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.69/0.88      inference('split', [status(esa)], ['0'])).
% 0.69/0.88  thf('65', plain,
% 0.69/0.88      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.69/0.88         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['63', '64'])).
% 0.69/0.88  thf('66', plain,
% 0.69/0.88      (~ (((sk_A) = (k1_xboole_0))) | ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.69/0.88      inference('sup-', [status(thm)], ['62', '65'])).
% 0.69/0.88  thf('67', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.69/0.88      inference('split', [status(esa)], ['39'])).
% 0.69/0.88  thf('68', plain,
% 0.69/0.88      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.69/0.88       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 0.69/0.88      inference('split', [status(esa)], ['0'])).
% 0.69/0.88  thf('69', plain,
% 0.69/0.88      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.69/0.88      inference('sat_resolution*', [status(thm)], ['4', '42', '66', '67', '68'])).
% 0.69/0.88  thf('70', plain,
% 0.69/0.88      (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.69/0.88      inference('simpl_trail', [status(thm)], ['1', '69'])).
% 0.69/0.88  thf('71', plain,
% 0.69/0.88      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['9', '16'])).
% 0.69/0.88  thf('72', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.69/0.88      inference('sup-', [status(thm)], ['18', '29'])).
% 0.69/0.88  thf('73', plain,
% 0.69/0.88      (![X29 : $i, X30 : $i]:
% 0.69/0.88         (~ (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 0.69/0.88          | (m1_subset_1 @ X29 @ 
% 0.69/0.88             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X29) @ X30)))
% 0.69/0.88          | ~ (v1_funct_1 @ X29)
% 0.69/0.88          | ~ (v1_relat_1 @ X29))),
% 0.69/0.88      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.69/0.88  thf('74', plain,
% 0.69/0.88      ((~ (v1_relat_1 @ sk_D)
% 0.69/0.88        | ~ (v1_funct_1 @ sk_D)
% 0.69/0.88        | (m1_subset_1 @ sk_D @ 
% 0.69/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['72', '73'])).
% 0.69/0.88  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 0.69/0.88      inference('sup-', [status(thm)], ['24', '25'])).
% 0.69/0.88  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('77', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ 
% 0.69/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 0.69/0.88      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.69/0.88  thf(t3_subset, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.69/0.88  thf('78', plain,
% 0.69/0.88      (![X7 : $i, X8 : $i]:
% 0.69/0.88         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.69/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.69/0.88  thf('79', plain,
% 0.69/0.88      ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C))),
% 0.69/0.88      inference('sup-', [status(thm)], ['77', '78'])).
% 0.69/0.88  thf('80', plain,
% 0.69/0.88      (((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))
% 0.69/0.88        | ((sk_B) = (k1_xboole_0)))),
% 0.69/0.88      inference('sup+', [status(thm)], ['71', '79'])).
% 0.69/0.88  thf('81', plain,
% 0.69/0.88      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.69/0.88      inference('split', [status(esa)], ['39'])).
% 0.69/0.88  thf('82', plain,
% 0.69/0.88      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('demod', [status(thm)], ['53', '59'])).
% 0.69/0.88  thf('83', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ 
% 0.69/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 0.69/0.88      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.69/0.88  thf('84', plain,
% 0.69/0.88      (((m1_subset_1 @ sk_D @ 
% 0.69/0.88         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.69/0.88         <= ((((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup+', [status(thm)], ['82', '83'])).
% 0.69/0.88  thf('85', plain,
% 0.69/0.88      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('split', [status(esa)], ['39'])).
% 0.69/0.88  thf('86', plain,
% 0.69/0.88      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.69/0.88         <= (~
% 0.69/0.88             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.69/0.88      inference('split', [status(esa)], ['0'])).
% 0.69/0.88  thf('87', plain,
% 0.69/0.88      ((~ (m1_subset_1 @ sk_D @ 
% 0.69/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.69/0.88         <= (~
% 0.69/0.88             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.69/0.88             (((sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['85', '86'])).
% 0.69/0.88  thf('88', plain,
% 0.69/0.88      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.69/0.88       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['84', '87'])).
% 0.69/0.88  thf('89', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.69/0.88      inference('sat_resolution*', [status(thm)],
% 0.69/0.88                ['4', '42', '66', '68', '88', '67'])).
% 0.69/0.88  thf('90', plain, (((sk_B) != (k1_xboole_0))),
% 0.69/0.88      inference('simpl_trail', [status(thm)], ['81', '89'])).
% 0.69/0.88  thf('91', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.69/0.88      inference('simplify_reflect-', [status(thm)], ['80', '90'])).
% 0.69/0.88  thf('92', plain,
% 0.69/0.88      (![X7 : $i, X9 : $i]:
% 0.69/0.88         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.69/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.69/0.88  thf('93', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['91', '92'])).
% 0.69/0.88  thf('94', plain, ($false), inference('demod', [status(thm)], ['70', '93'])).
% 0.69/0.88  
% 0.69/0.88  % SZS output end Refutation
% 0.69/0.88  
% 0.69/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
