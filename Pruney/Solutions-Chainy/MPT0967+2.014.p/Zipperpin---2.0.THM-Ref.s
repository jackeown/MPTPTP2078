%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1k3eDa3u8R

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:13 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 590 expanded)
%              Number of leaves         :   34 ( 174 expanded)
%              Depth                    :   25
%              Number of atoms          : 1111 (8756 expanded)
%              Number of equality atoms :   92 ( 562 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    r1_tarski @ sk_B @ sk_C ),
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

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['12','15'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

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

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('28',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('34',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('39',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['7','18'])).

thf('48',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) )
        | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('55',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24
       != ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('57',plain,
    ( ( ( k1_xboole_0
       != ( k1_relat_1 @ sk_D ) )
      | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0 )
      | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('59',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('62',plain,(
    ! [X22: $i] :
      ( zip_tseitin_0 @ X22 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','62'])).

thf('64',plain,
    ( ( ( k1_xboole_0
       != ( k1_relat_1 @ sk_D ) )
      | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('66',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('69',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('71',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('72',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','72'])).

thf('74',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('75',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('76',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X22: $i] :
      ( zip_tseitin_0 @ X22 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('78',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','79'])).

thf('81',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('83',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['44'])).

thf('84',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('87',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('88',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['44'])).

thf('89',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['44'])).

thf('92',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('93',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['46','85','90','91','92'])).

thf('94',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['42','93'])).

thf('95',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['40','94'])).

thf('96',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['35','95'])).

thf('97',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['28','96'])).

thf('98',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24
       != ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('99',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['44'])).

thf('102',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('103',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['44'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['44'])).

thf('106',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['46','104','105'])).

thf('107',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['101','106'])).

thf('108',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['100','107'])).

thf('109',plain,(
    ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['25','108'])).

thf('110',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','109'])).

thf('111',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['42','93'])).

thf('112',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['110','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1k3eDa3u8R
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.42/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.59  % Solved by: fo/fo7.sh
% 0.42/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.59  % done 233 iterations in 0.134s
% 0.42/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.59  % SZS output start Refutation
% 0.42/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.42/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.42/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.42/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.59  thf(t9_funct_2, conjecture,
% 0.42/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.42/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.59       ( ( r1_tarski @ B @ C ) =>
% 0.42/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.42/0.59           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.42/0.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.59        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.42/0.59            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.59          ( ( r1_tarski @ B @ C ) =>
% 0.42/0.59            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.42/0.59              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.42/0.59                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.42/0.59    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.42/0.59  thf('0', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(d1_funct_2, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.42/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.42/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_1, axiom,
% 0.42/0.59    (![B:$i,A:$i]:
% 0.42/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.42/0.59  thf('1', plain,
% 0.42/0.59      (![X22 : $i, X23 : $i]:
% 0.42/0.59         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.42/0.59  thf('2', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.42/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.59  thf(d10_xboole_0, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.59  thf('3', plain,
% 0.42/0.59      (![X0 : $i, X2 : $i]:
% 0.42/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.42/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.59  thf('4', plain,
% 0.42/0.59      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.59  thf('5', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.59         (~ (r1_tarski @ X1 @ X0)
% 0.42/0.59          | (zip_tseitin_0 @ X0 @ X2)
% 0.42/0.59          | ((X1) = (k1_xboole_0)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['1', '4'])).
% 0.42/0.59  thf('6', plain,
% 0.42/0.59      (![X0 : $i]: (((sk_B) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_C @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['0', '5'])).
% 0.42/0.59  thf('7', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('8', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(cc2_relset_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.42/0.59  thf('9', plain,
% 0.42/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.59         ((v5_relat_1 @ X12 @ X14)
% 0.42/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.42/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.59  thf('10', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.42/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.59  thf(d19_relat_1, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( v1_relat_1 @ B ) =>
% 0.42/0.59       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.42/0.59  thf('11', plain,
% 0.42/0.59      (![X7 : $i, X8 : $i]:
% 0.42/0.59         (~ (v5_relat_1 @ X7 @ X8)
% 0.42/0.59          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.42/0.59          | ~ (v1_relat_1 @ X7))),
% 0.42/0.59      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.42/0.59  thf('12', plain,
% 0.42/0.59      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.42/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.42/0.59  thf('13', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(cc1_relset_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( v1_relat_1 @ C ) ))).
% 0.42/0.59  thf('14', plain,
% 0.42/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.59         ((v1_relat_1 @ X9)
% 0.42/0.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.42/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.59  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.42/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.42/0.59  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.42/0.59      inference('demod', [status(thm)], ['12', '15'])).
% 0.42/0.59  thf(t1_xboole_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.42/0.59       ( r1_tarski @ A @ C ) ))).
% 0.42/0.59  thf('17', plain,
% 0.42/0.59      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.59         (~ (r1_tarski @ X3 @ X4)
% 0.42/0.59          | ~ (r1_tarski @ X4 @ X5)
% 0.42/0.59          | (r1_tarski @ X3 @ X5))),
% 0.42/0.59      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.42/0.59  thf('18', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.59  thf('19', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.42/0.59      inference('sup-', [status(thm)], ['7', '18'])).
% 0.42/0.59  thf('20', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(t14_relset_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.42/0.59       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.42/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.42/0.59  thf('21', plain,
% 0.42/0.59      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.42/0.59         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.42/0.59          | (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.42/0.59          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.42/0.59      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.42/0.59  thf('22', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.42/0.59          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.59  thf('23', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['19', '22'])).
% 0.42/0.59  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.42/0.59  thf(zf_stmt_3, axiom,
% 0.42/0.59    (![C:$i,B:$i,A:$i]:
% 0.42/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.42/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.42/0.59  thf(zf_stmt_5, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.42/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.42/0.59  thf('24', plain,
% 0.42/0.59      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.42/0.59         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.42/0.59          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.42/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.59  thf('25', plain,
% 0.42/0.59      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.42/0.59  thf('26', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['19', '22'])).
% 0.42/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.42/0.59  thf('27', plain,
% 0.42/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.59         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.42/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.42/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.59  thf('28', plain,
% 0.42/0.59      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.42/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.42/0.59  thf('29', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('30', plain,
% 0.42/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.59         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.42/0.59          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.42/0.59          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.59  thf('31', plain,
% 0.42/0.59      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.42/0.59        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.42/0.59  thf('32', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('33', plain,
% 0.42/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.59         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.42/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.42/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.59  thf('34', plain,
% 0.42/0.59      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.42/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.42/0.59  thf('35', plain,
% 0.42/0.59      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.42/0.59      inference('demod', [status(thm)], ['31', '34'])).
% 0.42/0.59  thf('36', plain,
% 0.42/0.59      (![X22 : $i, X23 : $i]:
% 0.42/0.59         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.59  thf('37', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('38', plain,
% 0.42/0.59      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.42/0.59         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.42/0.59          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.42/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.59  thf('39', plain,
% 0.42/0.59      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['37', '38'])).
% 0.42/0.59  thf('40', plain,
% 0.42/0.59      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['36', '39'])).
% 0.42/0.59  thf('41', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('42', plain,
% 0.42/0.59      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.42/0.59      inference('split', [status(esa)], ['41'])).
% 0.42/0.59  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('44', plain,
% 0.42/0.59      ((~ (v1_funct_1 @ sk_D)
% 0.42/0.59        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.42/0.59        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('45', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.42/0.59      inference('split', [status(esa)], ['44'])).
% 0.42/0.59  thf('46', plain, (((v1_funct_1 @ sk_D))),
% 0.42/0.59      inference('sup-', [status(thm)], ['43', '45'])).
% 0.42/0.59  thf('47', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.42/0.59      inference('sup-', [status(thm)], ['7', '18'])).
% 0.42/0.59  thf('48', plain,
% 0.42/0.59      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('split', [status(esa)], ['41'])).
% 0.42/0.59  thf('49', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('50', plain,
% 0.42/0.59      (((m1_subset_1 @ sk_D @ 
% 0.42/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup+', [status(thm)], ['48', '49'])).
% 0.42/0.59  thf('51', plain,
% 0.42/0.59      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.42/0.59         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.42/0.59          | (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.42/0.59          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.42/0.59      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.42/0.59  thf('52', plain,
% 0.42/0.59      ((![X0 : $i]:
% 0.42/0.59          ((m1_subset_1 @ sk_D @ 
% 0.42/0.59            (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))
% 0.42/0.59           | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0)))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.42/0.59  thf('53', plain,
% 0.42/0.59      (((m1_subset_1 @ sk_D @ 
% 0.42/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['47', '52'])).
% 0.42/0.59  thf('54', plain,
% 0.42/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.59         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.42/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.42/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.59  thf('55', plain,
% 0.42/0.59      ((((k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['53', '54'])).
% 0.42/0.59  thf('56', plain,
% 0.42/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.59         (((X24) != (k1_relset_1 @ X24 @ X25 @ X26))
% 0.42/0.59          | (v1_funct_2 @ X26 @ X24 @ X25)
% 0.42/0.59          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.59  thf('57', plain,
% 0.42/0.59      (((((k1_xboole_0) != (k1_relat_1 @ sk_D))
% 0.42/0.59         | ~ (zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0)
% 0.42/0.59         | (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C)))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['55', '56'])).
% 0.42/0.59  thf('58', plain,
% 0.42/0.59      (((m1_subset_1 @ sk_D @ 
% 0.42/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['47', '52'])).
% 0.42/0.59  thf('59', plain,
% 0.42/0.59      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.42/0.59         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.42/0.59          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.42/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.59  thf('60', plain,
% 0.42/0.59      ((((zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0)
% 0.42/0.59         | ~ (zip_tseitin_0 @ sk_C @ k1_xboole_0)))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.42/0.59  thf('61', plain,
% 0.42/0.59      (![X22 : $i, X23 : $i]:
% 0.42/0.59         ((zip_tseitin_0 @ X22 @ X23) | ((X23) != (k1_xboole_0)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.59  thf('62', plain, (![X22 : $i]: (zip_tseitin_0 @ X22 @ k1_xboole_0)),
% 0.42/0.59      inference('simplify', [status(thm)], ['61'])).
% 0.42/0.59  thf('63', plain,
% 0.42/0.59      (((zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('demod', [status(thm)], ['60', '62'])).
% 0.42/0.59  thf('64', plain,
% 0.42/0.59      (((((k1_xboole_0) != (k1_relat_1 @ sk_D))
% 0.42/0.59         | (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C)))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('demod', [status(thm)], ['57', '63'])).
% 0.42/0.59  thf('65', plain,
% 0.42/0.59      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('split', [status(esa)], ['41'])).
% 0.42/0.59  thf('66', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('67', plain,
% 0.42/0.59      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup+', [status(thm)], ['65', '66'])).
% 0.42/0.59  thf('68', plain,
% 0.42/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.59         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.42/0.59          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.42/0.59          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.59  thf('69', plain,
% 0.42/0.59      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.42/0.59         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['67', '68'])).
% 0.42/0.59  thf('70', plain,
% 0.42/0.59      (((m1_subset_1 @ sk_D @ 
% 0.42/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup+', [status(thm)], ['48', '49'])).
% 0.42/0.59  thf('71', plain,
% 0.42/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.59         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.42/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.42/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.59  thf('72', plain,
% 0.42/0.59      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['70', '71'])).
% 0.42/0.59  thf('73', plain,
% 0.42/0.59      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.42/0.59         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('demod', [status(thm)], ['69', '72'])).
% 0.42/0.59  thf('74', plain,
% 0.42/0.59      (((m1_subset_1 @ sk_D @ 
% 0.42/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup+', [status(thm)], ['48', '49'])).
% 0.42/0.59  thf('75', plain,
% 0.42/0.59      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.42/0.59         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.42/0.59          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.42/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.59  thf('76', plain,
% 0.42/0.59      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.42/0.59         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['74', '75'])).
% 0.42/0.59  thf('77', plain, (![X22 : $i]: (zip_tseitin_0 @ X22 @ k1_xboole_0)),
% 0.42/0.59      inference('simplify', [status(thm)], ['61'])).
% 0.42/0.59  thf('78', plain,
% 0.42/0.59      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('demod', [status(thm)], ['76', '77'])).
% 0.42/0.59  thf('79', plain,
% 0.42/0.59      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('demod', [status(thm)], ['73', '78'])).
% 0.42/0.59  thf('80', plain,
% 0.42/0.59      (((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.59         | (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C)))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('demod', [status(thm)], ['64', '79'])).
% 0.42/0.59  thf('81', plain,
% 0.42/0.59      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('simplify', [status(thm)], ['80'])).
% 0.42/0.59  thf('82', plain,
% 0.42/0.59      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('split', [status(esa)], ['41'])).
% 0.42/0.59  thf('83', plain,
% 0.42/0.59      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.42/0.59         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.42/0.59      inference('split', [status(esa)], ['44'])).
% 0.42/0.59  thf('84', plain,
% 0.42/0.59      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.42/0.59         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['82', '83'])).
% 0.42/0.59  thf('85', plain,
% 0.42/0.59      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['81', '84'])).
% 0.42/0.59  thf('86', plain,
% 0.42/0.59      (((m1_subset_1 @ sk_D @ 
% 0.42/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['47', '52'])).
% 0.42/0.59  thf('87', plain,
% 0.42/0.59      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('split', [status(esa)], ['41'])).
% 0.42/0.59  thf('88', plain,
% 0.42/0.59      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.42/0.59         <= (~
% 0.42/0.59             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.42/0.59      inference('split', [status(esa)], ['44'])).
% 0.42/0.59  thf('89', plain,
% 0.42/0.59      ((~ (m1_subset_1 @ sk_D @ 
% 0.42/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.42/0.59         <= (~
% 0.42/0.59             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.42/0.59             (((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['87', '88'])).
% 0.42/0.59  thf('90', plain,
% 0.42/0.59      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.42/0.59       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['86', '89'])).
% 0.42/0.59  thf('91', plain,
% 0.42/0.59      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.42/0.59       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 0.42/0.59      inference('split', [status(esa)], ['44'])).
% 0.42/0.59  thf('92', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.42/0.59      inference('split', [status(esa)], ['41'])).
% 0.42/0.59  thf('93', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.42/0.59      inference('sat_resolution*', [status(thm)],
% 0.42/0.59                ['46', '85', '90', '91', '92'])).
% 0.42/0.59  thf('94', plain, (((sk_B) != (k1_xboole_0))),
% 0.42/0.59      inference('simpl_trail', [status(thm)], ['42', '93'])).
% 0.42/0.59  thf('95', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.42/0.59      inference('simplify_reflect-', [status(thm)], ['40', '94'])).
% 0.42/0.59  thf('96', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.42/0.59      inference('demod', [status(thm)], ['35', '95'])).
% 0.42/0.59  thf('97', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 0.42/0.59      inference('demod', [status(thm)], ['28', '96'])).
% 0.42/0.59  thf('98', plain,
% 0.42/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.59         (((X24) != (k1_relset_1 @ X24 @ X25 @ X26))
% 0.42/0.59          | (v1_funct_2 @ X26 @ X24 @ X25)
% 0.42/0.59          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.59  thf('99', plain,
% 0.42/0.59      ((((sk_A) != (sk_A))
% 0.42/0.59        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.42/0.59        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.42/0.59      inference('sup-', [status(thm)], ['97', '98'])).
% 0.42/0.59  thf('100', plain,
% 0.42/0.59      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.42/0.59        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.42/0.59      inference('simplify', [status(thm)], ['99'])).
% 0.42/0.59  thf('101', plain,
% 0.42/0.59      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.42/0.59         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.42/0.59      inference('split', [status(esa)], ['44'])).
% 0.42/0.59  thf('102', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['19', '22'])).
% 0.42/0.59  thf('103', plain,
% 0.42/0.59      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.42/0.59         <= (~
% 0.42/0.59             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.42/0.59      inference('split', [status(esa)], ['44'])).
% 0.42/0.59  thf('104', plain,
% 0.42/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['102', '103'])).
% 0.42/0.59  thf('105', plain,
% 0.42/0.59      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.42/0.59       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.42/0.59       ~ ((v1_funct_1 @ sk_D))),
% 0.42/0.59      inference('split', [status(esa)], ['44'])).
% 0.42/0.59  thf('106', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.42/0.59      inference('sat_resolution*', [status(thm)], ['46', '104', '105'])).
% 0.42/0.59  thf('107', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.42/0.59      inference('simpl_trail', [status(thm)], ['101', '106'])).
% 0.42/0.59  thf('108', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 0.42/0.59      inference('clc', [status(thm)], ['100', '107'])).
% 0.42/0.59  thf('109', plain, (~ (zip_tseitin_0 @ sk_C @ sk_A)),
% 0.42/0.59      inference('clc', [status(thm)], ['25', '108'])).
% 0.42/0.59  thf('110', plain, (((sk_B) = (k1_xboole_0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['6', '109'])).
% 0.42/0.59  thf('111', plain, (((sk_B) != (k1_xboole_0))),
% 0.42/0.59      inference('simpl_trail', [status(thm)], ['42', '93'])).
% 0.42/0.59  thf('112', plain, ($false),
% 0.42/0.59      inference('simplify_reflect-', [status(thm)], ['110', '111'])).
% 0.42/0.59  
% 0.42/0.59  % SZS output end Refutation
% 0.42/0.59  
% 0.42/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
