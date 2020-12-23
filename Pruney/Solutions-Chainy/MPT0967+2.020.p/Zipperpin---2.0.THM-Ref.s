%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wqGu3RwmaY

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:13 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 474 expanded)
%              Number of leaves         :   33 ( 137 expanded)
%              Depth                    :   20
%              Number of atoms          : 1036 (6952 expanded)
%              Number of equality atoms :   92 ( 586 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X26 )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X25 ) @ X26 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','35'])).

thf('37',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('46',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('50',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('55',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('57',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X18 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,(
    ! [X17: $i] :
      ( zip_tseitin_0 @ X17 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','60'])).

thf('62',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','62'])).

thf('64',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19
       != ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ~ ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
        | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('67',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('68',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X17: $i] :
      ( zip_tseitin_0 @ X17 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','72'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('76',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('80',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('82',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('88',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','78','85','86','87'])).

thf('89',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['38','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['36','89'])).

thf('91',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('92',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('94',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','92','93'])).

thf('95',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','94'])).

thf('96',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('97',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['18','29'])).

thf('98',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X26 )
      | ( v1_funct_2 @ X25 @ ( k1_relat_1 @ X25 ) @ X26 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('101',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','102'])).

thf('104',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['38','88'])).

thf('105',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['103','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['95','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wqGu3RwmaY
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:05:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 267 iterations in 0.207s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.66  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.47/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.47/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.66  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.66  thf(t9_funct_2, conjecture,
% 0.47/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.66     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.66       ( ( r1_tarski @ B @ C ) =>
% 0.47/0.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.66           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.47/0.66             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.66        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.66            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.66          ( ( r1_tarski @ B @ C ) =>
% 0.47/0.66            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.66              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.47/0.66                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.47/0.66  thf('0', plain,
% 0.47/0.66      ((~ (v1_funct_1 @ sk_D)
% 0.47/0.66        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.47/0.66        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.47/0.66         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.47/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.66  thf(d1_funct_2, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.66           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.47/0.66             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.47/0.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.66           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.47/0.66             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_1, axiom,
% 0.47/0.66    (![B:$i,A:$i]:
% 0.47/0.66     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.66       ( zip_tseitin_0 @ B @ A ) ))).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      (![X17 : $i, X18 : $i]:
% 0.47/0.66         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.47/0.66  thf(zf_stmt_3, axiom,
% 0.47/0.66    (![C:$i,B:$i,A:$i]:
% 0.47/0.66     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.47/0.66       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.47/0.66  thf(zf_stmt_5, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.47/0.66         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.66           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.66             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.47/0.66         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.47/0.66          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.47/0.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['5', '8'])).
% 0.47/0.66  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('11', plain,
% 0.47/0.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.66         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.47/0.66          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.47/0.66          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.47/0.66        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.66         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.47/0.66          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.47/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.47/0.66      inference('demod', [status(thm)], ['12', '15'])).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['9', '16'])).
% 0.47/0.66  thf('18', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(cc2_relset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.66         ((v5_relat_1 @ X11 @ X13)
% 0.47/0.66          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.66  thf('21', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.47/0.66      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.66  thf(d19_relat_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ B ) =>
% 0.47/0.66       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.66  thf('22', plain,
% 0.47/0.66      (![X6 : $i, X7 : $i]:
% 0.47/0.66         (~ (v5_relat_1 @ X6 @ X7)
% 0.47/0.66          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.47/0.66          | ~ (v1_relat_1 @ X6))),
% 0.47/0.66      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.47/0.66  thf('23', plain,
% 0.47/0.66      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.66  thf('24', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(cc1_relset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( v1_relat_1 @ C ) ))).
% 0.47/0.66  thf('25', plain,
% 0.47/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.66         ((v1_relat_1 @ X8)
% 0.47/0.66          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.66  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.66  thf('27', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.47/0.66      inference('demod', [status(thm)], ['23', '26'])).
% 0.47/0.66  thf(t1_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.47/0.66       ( r1_tarski @ A @ C ) ))).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (~ (r1_tarski @ X0 @ X1)
% 0.47/0.66          | ~ (r1_tarski @ X1 @ X2)
% 0.47/0.66          | (r1_tarski @ X0 @ X2))),
% 0.47/0.66      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.66  thf('30', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.47/0.66      inference('sup-', [status(thm)], ['18', '29'])).
% 0.47/0.66  thf(t4_funct_2, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.66       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.47/0.66         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.47/0.66           ( m1_subset_1 @
% 0.47/0.66             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.47/0.66  thf('31', plain,
% 0.47/0.66      (![X25 : $i, X26 : $i]:
% 0.47/0.66         (~ (r1_tarski @ (k2_relat_1 @ X25) @ X26)
% 0.47/0.66          | (m1_subset_1 @ X25 @ 
% 0.47/0.66             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X25) @ X26)))
% 0.47/0.66          | ~ (v1_funct_1 @ X25)
% 0.47/0.66          | ~ (v1_relat_1 @ X25))),
% 0.47/0.66      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      ((~ (v1_relat_1 @ sk_D)
% 0.47/0.66        | ~ (v1_funct_1 @ sk_D)
% 0.47/0.66        | (m1_subset_1 @ sk_D @ 
% 0.47/0.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.66  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.66  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D @ 
% 0.47/0.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 0.47/0.66      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.47/0.66        | ((sk_B) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['17', '35'])).
% 0.47/0.66  thf('37', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('38', plain,
% 0.47/0.66      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.47/0.66      inference('split', [status(esa)], ['37'])).
% 0.47/0.66  thf(t113_zfmisc_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.66  thf('39', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i]:
% 0.47/0.66         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.66  thf('40', plain,
% 0.47/0.66      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['39'])).
% 0.47/0.66  thf('41', plain,
% 0.47/0.66      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('split', [status(esa)], ['37'])).
% 0.47/0.66  thf('42', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('43', plain,
% 0.47/0.66      (((m1_subset_1 @ sk_D @ 
% 0.47/0.66         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.47/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['41', '42'])).
% 0.47/0.66  thf('44', plain,
% 0.47/0.66      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.47/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['40', '43'])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['39'])).
% 0.47/0.66  thf('46', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.66         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.47/0.66          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.66  thf('47', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.47/0.66          | ((k1_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k1_relat_1 @ X1)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['45', '46'])).
% 0.47/0.66  thf('48', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.47/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['44', '47'])).
% 0.47/0.66  thf('49', plain,
% 0.47/0.66      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('split', [status(esa)], ['37'])).
% 0.47/0.66  thf('50', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('51', plain,
% 0.47/0.66      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.47/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['49', '50'])).
% 0.47/0.66  thf('52', plain,
% 0.47/0.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.66         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.47/0.66          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.47/0.66          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.66  thf('53', plain,
% 0.47/0.66      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.47/0.66         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 0.47/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['51', '52'])).
% 0.47/0.66  thf('54', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.47/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['44', '47'])).
% 0.47/0.66  thf('55', plain,
% 0.47/0.66      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.47/0.66         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 0.47/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('demod', [status(thm)], ['53', '54'])).
% 0.47/0.66  thf('56', plain,
% 0.47/0.66      (((m1_subset_1 @ sk_D @ 
% 0.47/0.66         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.47/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['41', '42'])).
% 0.47/0.66  thf('57', plain,
% 0.47/0.66      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.47/0.66         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.47/0.66          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.47/0.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.66  thf('58', plain,
% 0.47/0.66      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.47/0.66         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.47/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['56', '57'])).
% 0.47/0.66  thf('59', plain,
% 0.47/0.66      (![X17 : $i, X18 : $i]:
% 0.47/0.66         ((zip_tseitin_0 @ X17 @ X18) | ((X18) != (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.66  thf('60', plain, (![X17 : $i]: (zip_tseitin_0 @ X17 @ k1_xboole_0)),
% 0.47/0.66      inference('simplify', [status(thm)], ['59'])).
% 0.47/0.66  thf('61', plain,
% 0.47/0.66      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 0.47/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('demod', [status(thm)], ['58', '60'])).
% 0.47/0.66  thf('62', plain,
% 0.47/0.66      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('demod', [status(thm)], ['55', '61'])).
% 0.47/0.66  thf('63', plain,
% 0.47/0.66      ((![X0 : $i]: ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_xboole_0)))
% 0.47/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('demod', [status(thm)], ['48', '62'])).
% 0.47/0.66  thf('64', plain,
% 0.47/0.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.66         (((X19) != (k1_relset_1 @ X19 @ X20 @ X21))
% 0.47/0.66          | (v1_funct_2 @ X21 @ X19 @ X20)
% 0.47/0.66          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.66  thf('65', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          (((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.66           | ~ (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0)
% 0.47/0.66           | (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0)))
% 0.47/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['63', '64'])).
% 0.47/0.66  thf('66', plain,
% 0.47/0.66      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.47/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['40', '43'])).
% 0.47/0.66  thf('67', plain,
% 0.47/0.66      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['39'])).
% 0.47/0.66  thf('68', plain,
% 0.47/0.66      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.47/0.66         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.47/0.66          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.47/0.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.66  thf('69', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.47/0.66          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.47/0.66          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['67', '68'])).
% 0.47/0.66  thf('70', plain, (![X17 : $i]: (zip_tseitin_0 @ X17 @ k1_xboole_0)),
% 0.47/0.66      inference('simplify', [status(thm)], ['59'])).
% 0.47/0.66  thf('71', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.47/0.66          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['69', '70'])).
% 0.47/0.66  thf('72', plain,
% 0.47/0.66      ((![X0 : $i]: (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0))
% 0.47/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['66', '71'])).
% 0.47/0.66  thf('73', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          (((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.66           | (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0)))
% 0.47/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('demod', [status(thm)], ['65', '72'])).
% 0.47/0.66  thf('74', plain,
% 0.47/0.66      ((![X0 : $i]: (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0))
% 0.47/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('simplify', [status(thm)], ['73'])).
% 0.47/0.66  thf('75', plain,
% 0.47/0.66      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('split', [status(esa)], ['37'])).
% 0.47/0.66  thf('76', plain,
% 0.47/0.66      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.47/0.66         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('77', plain,
% 0.47/0.66      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.47/0.66         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['75', '76'])).
% 0.47/0.66  thf('78', plain,
% 0.47/0.66      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['74', '77'])).
% 0.47/0.66  thf('79', plain,
% 0.47/0.66      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.47/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['40', '43'])).
% 0.47/0.66  thf('80', plain,
% 0.47/0.66      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['39'])).
% 0.47/0.66  thf('81', plain,
% 0.47/0.66      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('split', [status(esa)], ['37'])).
% 0.47/0.66  thf('82', plain,
% 0.47/0.66      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.47/0.66         <= (~
% 0.47/0.66             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('83', plain,
% 0.47/0.66      ((~ (m1_subset_1 @ sk_D @ 
% 0.47/0.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.47/0.66         <= (~
% 0.47/0.66             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.47/0.66             (((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['81', '82'])).
% 0.47/0.66  thf('84', plain,
% 0.47/0.66      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.47/0.66         <= (~
% 0.47/0.66             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.47/0.66             (((sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['80', '83'])).
% 0.47/0.66  thf('85', plain,
% 0.47/0.66      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.47/0.66       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['79', '84'])).
% 0.47/0.66  thf('86', plain,
% 0.47/0.66      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.47/0.66       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('87', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.47/0.66      inference('split', [status(esa)], ['37'])).
% 0.47/0.66  thf('88', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['4', '78', '85', '86', '87'])).
% 0.47/0.66  thf('89', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['38', '88'])).
% 0.47/0.66  thf('90', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['36', '89'])).
% 0.47/0.66  thf('91', plain,
% 0.47/0.66      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.47/0.66         <= (~
% 0.47/0.66             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('92', plain,
% 0.47/0.66      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['90', '91'])).
% 0.47/0.66  thf('93', plain,
% 0.47/0.66      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.47/0.66       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.47/0.66       ~ ((v1_funct_1 @ sk_D))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('94', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['4', '92', '93'])).
% 0.47/0.66  thf('95', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['1', '94'])).
% 0.47/0.66  thf('96', plain,
% 0.47/0.66      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['9', '16'])).
% 0.47/0.66  thf('97', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.47/0.66      inference('sup-', [status(thm)], ['18', '29'])).
% 0.47/0.66  thf('98', plain,
% 0.47/0.66      (![X25 : $i, X26 : $i]:
% 0.47/0.66         (~ (r1_tarski @ (k2_relat_1 @ X25) @ X26)
% 0.47/0.66          | (v1_funct_2 @ X25 @ (k1_relat_1 @ X25) @ X26)
% 0.47/0.66          | ~ (v1_funct_1 @ X25)
% 0.47/0.66          | ~ (v1_relat_1 @ X25))),
% 0.47/0.66      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.47/0.66  thf('99', plain,
% 0.47/0.66      ((~ (v1_relat_1 @ sk_D)
% 0.47/0.66        | ~ (v1_funct_1 @ sk_D)
% 0.47/0.66        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C))),
% 0.47/0.66      inference('sup-', [status(thm)], ['97', '98'])).
% 0.47/0.66  thf('100', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.66  thf('101', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('102', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.47/0.66      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.47/0.66  thf('103', plain,
% 0.47/0.66      (((v1_funct_2 @ sk_D @ sk_A @ sk_C) | ((sk_B) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['96', '102'])).
% 0.47/0.66  thf('104', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['38', '88'])).
% 0.47/0.66  thf('105', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['103', '104'])).
% 0.47/0.66  thf('106', plain, ($false), inference('demod', [status(thm)], ['95', '105'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.52/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
