%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hOkxN2SFNq

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:05 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  185 (7670 expanded)
%              Number of leaves         :   41 (2127 expanded)
%              Depth                    :   37
%              Number of atoms          : 1340 (115148 expanded)
%              Number of equality atoms :  104 (7301 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(t8_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
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
       => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(demod,[status(thm)],['0','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X26 )
      | ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
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

thf('15',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('23',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('36',plain,
    ( ( v4_relat_1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v4_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('38',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('40',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('41',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('48',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C_1 @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('50',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29
       != ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('52',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
      | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('55',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_C_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X28 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('58',plain,(
    ! [X27: $i] :
      ( zip_tseitin_0 @ X27 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','58'])).

thf('60',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','59'])).

thf('61',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('62',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['29'])).

thf('63',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('67',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['29'])).

thf('68',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['29'])).

thf('71',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('72',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['31','64','69','70','71'])).

thf('73',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['27','72'])).

thf('74',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['25','73'])).

thf('75',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['20','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['13','75'])).

thf('77',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('78',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('80',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('81',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_C_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['20','74'])).

thf('83',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['20','74'])).

thf('84',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29
       != ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('86',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['29'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['13','75'])).

thf('90',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['29'])).

thf('91',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['29'])).

thf('93',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['31','91','92'])).

thf('94',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['88','93'])).

thf('95',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['87','94'])).

thf('96',plain,(
    ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['78','95'])).

thf('97',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('98',plain,(
    ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['78','95'])).

thf('99',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','99'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('101',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('102',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('103',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ( X37 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X38 @ X35 ) @ ( k2_relset_1 @ X36 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['27','72'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['107','108'])).

thf('110',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('112',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
    | ( sk_C_1
      = ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('114',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('115',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k2_relat_1 @ sk_D ) )
    | ( sk_C_1
      = ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('117',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('118',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('119',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('123',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['20','74'])).

thf('124',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('125',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ sk_A @ X0 @ sk_D )
      = ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ sk_A @ X0 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ ( sk_C @ X0 @ sk_A ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','130'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('132',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( k1_funct_1 @ sk_D @ ( sk_C @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('137',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('139',plain,(
    ! [X27: $i] :
      ( zip_tseitin_0 @ X27 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['140'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['100','137','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hOkxN2SFNq
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.76/1.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/1.00  % Solved by: fo/fo7.sh
% 0.76/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/1.00  % done 533 iterations in 0.541s
% 0.76/1.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/1.00  % SZS output start Refutation
% 0.76/1.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/1.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/1.00  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.76/1.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/1.00  thf(sk_B_type, type, sk_B: $i).
% 0.76/1.00  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.76/1.00  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/1.00  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/1.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/1.00  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.76/1.00  thf(sk_D_type, type, sk_D: $i).
% 0.76/1.00  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.76/1.00  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.76/1.00  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/1.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/1.00  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.76/1.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/1.00  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.76/1.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/1.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/1.00  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.76/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.76/1.00  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.76/1.00  thf(t8_funct_2, conjecture,
% 0.76/1.00    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/1.00     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.76/1.00         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/1.00       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.76/1.00         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.76/1.00           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.76/1.00             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.76/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.76/1.00    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.76/1.00        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.76/1.00            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/1.00          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.76/1.00            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.76/1.00              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.76/1.00                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.76/1.00    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 0.76/1.00  thf('0', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_C_1)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('1', plain,
% 0.76/1.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf(redefinition_k2_relset_1, axiom,
% 0.76/1.00    (![A:$i,B:$i,C:$i]:
% 0.76/1.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/1.00       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.76/1.00  thf('2', plain,
% 0.76/1.00      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.76/1.00         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.76/1.00          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.76/1.00      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.76/1.00  thf('3', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.76/1.00      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/1.00  thf('4', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 0.76/1.00      inference('demod', [status(thm)], ['0', '3'])).
% 0.76/1.00  thf(d10_xboole_0, axiom,
% 0.76/1.00    (![A:$i,B:$i]:
% 0.76/1.00     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/1.00  thf('5', plain,
% 0.76/1.00      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.76/1.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/1.00  thf('6', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.76/1.00      inference('simplify', [status(thm)], ['5'])).
% 0.76/1.00  thf(t11_relset_1, axiom,
% 0.76/1.00    (![A:$i,B:$i,C:$i]:
% 0.76/1.00     ( ( v1_relat_1 @ C ) =>
% 0.76/1.00       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.76/1.00           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.76/1.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.76/1.00  thf('7', plain,
% 0.76/1.00      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.76/1.00         (~ (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 0.76/1.00          | ~ (r1_tarski @ (k2_relat_1 @ X24) @ X26)
% 0.76/1.00          | (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.76/1.00          | ~ (v1_relat_1 @ X24))),
% 0.76/1.00      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.76/1.00  thf('8', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i]:
% 0.76/1.00         (~ (v1_relat_1 @ X0)
% 0.76/1.00          | (m1_subset_1 @ X0 @ 
% 0.76/1.00             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.76/1.00          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.76/1.00      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/1.00  thf('9', plain,
% 0.76/1.00      (((m1_subset_1 @ sk_D @ 
% 0.76/1.00         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C_1)))
% 0.76/1.00        | ~ (v1_relat_1 @ sk_D))),
% 0.76/1.00      inference('sup-', [status(thm)], ['4', '8'])).
% 0.76/1.00  thf('10', plain,
% 0.76/1.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf(cc1_relset_1, axiom,
% 0.76/1.00    (![A:$i,B:$i,C:$i]:
% 0.76/1.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/1.00       ( v1_relat_1 @ C ) ))).
% 0.76/1.00  thf('11', plain,
% 0.76/1.00      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.76/1.00         ((v1_relat_1 @ X12)
% 0.76/1.00          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.76/1.00      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.76/1.00  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 0.76/1.00      inference('sup-', [status(thm)], ['10', '11'])).
% 0.76/1.00  thf('13', plain,
% 0.76/1.00      ((m1_subset_1 @ sk_D @ 
% 0.76/1.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C_1)))),
% 0.76/1.00      inference('demod', [status(thm)], ['9', '12'])).
% 0.76/1.00  thf('14', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf(d1_funct_2, axiom,
% 0.76/1.00    (![A:$i,B:$i,C:$i]:
% 0.76/1.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/1.00       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/1.00           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.76/1.00             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.76/1.00         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/1.00           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.76/1.00             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.76/1.00  thf(zf_stmt_1, axiom,
% 0.76/1.00    (![C:$i,B:$i,A:$i]:
% 0.76/1.00     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.76/1.00       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.76/1.00  thf('15', plain,
% 0.76/1.00      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.76/1.00         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.76/1.00          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.76/1.00          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/1.00  thf('16', plain,
% 0.76/1.00      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.76/1.00        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.76/1.00      inference('sup-', [status(thm)], ['14', '15'])).
% 0.76/1.00  thf('17', plain,
% 0.76/1.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf(redefinition_k1_relset_1, axiom,
% 0.76/1.00    (![A:$i,B:$i,C:$i]:
% 0.76/1.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/1.00       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.76/1.00  thf('18', plain,
% 0.76/1.00      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.76/1.00         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.76/1.00          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.76/1.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/1.00  thf('19', plain,
% 0.76/1.00      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.76/1.00      inference('sup-', [status(thm)], ['17', '18'])).
% 0.76/1.00  thf('20', plain,
% 0.76/1.00      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.76/1.00      inference('demod', [status(thm)], ['16', '19'])).
% 0.76/1.00  thf(zf_stmt_2, axiom,
% 0.76/1.00    (![B:$i,A:$i]:
% 0.76/1.00     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/1.00       ( zip_tseitin_0 @ B @ A ) ))).
% 0.76/1.00  thf('21', plain,
% 0.76/1.00      (![X27 : $i, X28 : $i]:
% 0.76/1.00         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/1.00  thf('22', plain,
% 0.76/1.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.76/1.00  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.76/1.00  thf(zf_stmt_5, axiom,
% 0.76/1.00    (![A:$i,B:$i,C:$i]:
% 0.76/1.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/1.00       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.76/1.00         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/1.00           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.76/1.00             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.76/1.00  thf('23', plain,
% 0.76/1.00      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.76/1.00         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.76/1.00          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.76/1.00          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/1.00  thf('24', plain,
% 0.76/1.00      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.76/1.00      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/1.00  thf('25', plain,
% 0.76/1.00      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.76/1.00      inference('sup-', [status(thm)], ['21', '24'])).
% 0.76/1.00  thf('26', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('27', plain,
% 0.76/1.00      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.76/1.00      inference('split', [status(esa)], ['26'])).
% 0.76/1.00  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('29', plain,
% 0.76/1.00      ((~ (v1_funct_1 @ sk_D)
% 0.76/1.00        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 0.76/1.00        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('30', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.76/1.00      inference('split', [status(esa)], ['29'])).
% 0.76/1.00  thf('31', plain, (((v1_funct_1 @ sk_D))),
% 0.76/1.00      inference('sup-', [status(thm)], ['28', '30'])).
% 0.76/1.00  thf('32', plain,
% 0.76/1.00      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('split', [status(esa)], ['26'])).
% 0.76/1.00  thf('33', plain,
% 0.76/1.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('34', plain,
% 0.76/1.00      (((m1_subset_1 @ sk_D @ 
% 0.76/1.00         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.76/1.00         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('sup+', [status(thm)], ['32', '33'])).
% 0.76/1.00  thf(cc2_relset_1, axiom,
% 0.76/1.00    (![A:$i,B:$i,C:$i]:
% 0.76/1.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/1.00       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.76/1.00  thf('35', plain,
% 0.76/1.00      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.76/1.00         ((v4_relat_1 @ X15 @ X16)
% 0.76/1.00          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.76/1.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/1.00  thf('36', plain,
% 0.76/1.00      (((v4_relat_1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['34', '35'])).
% 0.76/1.00  thf(d18_relat_1, axiom,
% 0.76/1.00    (![A:$i,B:$i]:
% 0.76/1.00     ( ( v1_relat_1 @ B ) =>
% 0.76/1.00       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.76/1.00  thf('37', plain,
% 0.76/1.00      (![X8 : $i, X9 : $i]:
% 0.76/1.00         (~ (v4_relat_1 @ X8 @ X9)
% 0.76/1.00          | (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.76/1.00          | ~ (v1_relat_1 @ X8))),
% 0.76/1.00      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.76/1.00  thf('38', plain,
% 0.76/1.00      (((~ (v1_relat_1 @ sk_D)
% 0.76/1.00         | (r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0)))
% 0.76/1.00         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['36', '37'])).
% 0.76/1.00  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 0.76/1.00      inference('sup-', [status(thm)], ['10', '11'])).
% 0.76/1.00  thf('40', plain,
% 0.76/1.00      (((r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0))
% 0.76/1.00         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('demod', [status(thm)], ['38', '39'])).
% 0.76/1.00  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.76/1.00  thf('41', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.76/1.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.76/1.00  thf('42', plain,
% 0.76/1.00      (![X4 : $i, X6 : $i]:
% 0.76/1.00         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.76/1.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/1.00  thf('43', plain,
% 0.76/1.00      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.76/1.00      inference('sup-', [status(thm)], ['41', '42'])).
% 0.76/1.00  thf('44', plain,
% 0.76/1.00      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['40', '43'])).
% 0.76/1.00  thf('45', plain,
% 0.76/1.00      ((m1_subset_1 @ sk_D @ 
% 0.76/1.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C_1)))),
% 0.76/1.00      inference('demod', [status(thm)], ['9', '12'])).
% 0.76/1.00  thf('46', plain,
% 0.76/1.00      (((m1_subset_1 @ sk_D @ 
% 0.76/1.00         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 0.76/1.00         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('sup+', [status(thm)], ['44', '45'])).
% 0.76/1.00  thf('47', plain,
% 0.76/1.00      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.76/1.00         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.76/1.00          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.76/1.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/1.00  thf('48', plain,
% 0.76/1.00      ((((k1_relset_1 @ k1_xboole_0 @ sk_C_1 @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.76/1.00         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['46', '47'])).
% 0.76/1.00  thf('49', plain,
% 0.76/1.00      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['40', '43'])).
% 0.76/1.00  thf('50', plain,
% 0.76/1.00      ((((k1_relset_1 @ k1_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0)))
% 0.76/1.00         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('demod', [status(thm)], ['48', '49'])).
% 0.76/1.00  thf('51', plain,
% 0.76/1.00      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.76/1.00         (((X29) != (k1_relset_1 @ X29 @ X30 @ X31))
% 0.76/1.00          | (v1_funct_2 @ X31 @ X29 @ X30)
% 0.76/1.00          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/1.00  thf('52', plain,
% 0.76/1.00      (((((k1_xboole_0) != (k1_xboole_0))
% 0.76/1.00         | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ k1_xboole_0)
% 0.76/1.00         | (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1)))
% 0.76/1.00         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['50', '51'])).
% 0.76/1.00  thf('53', plain,
% 0.76/1.00      ((((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1)
% 0.76/1.00         | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ k1_xboole_0)))
% 0.76/1.00         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('simplify', [status(thm)], ['52'])).
% 0.76/1.00  thf('54', plain,
% 0.76/1.00      (((m1_subset_1 @ sk_D @ 
% 0.76/1.00         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 0.76/1.00         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('sup+', [status(thm)], ['44', '45'])).
% 0.76/1.00  thf('55', plain,
% 0.76/1.00      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.76/1.00         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.76/1.00          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.76/1.00          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/1.00  thf('56', plain,
% 0.76/1.00      ((((zip_tseitin_1 @ sk_D @ sk_C_1 @ k1_xboole_0)
% 0.76/1.00         | ~ (zip_tseitin_0 @ sk_C_1 @ k1_xboole_0)))
% 0.76/1.00         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['54', '55'])).
% 0.76/1.00  thf('57', plain,
% 0.76/1.00      (![X27 : $i, X28 : $i]:
% 0.76/1.00         ((zip_tseitin_0 @ X27 @ X28) | ((X28) != (k1_xboole_0)))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/1.00  thf('58', plain, (![X27 : $i]: (zip_tseitin_0 @ X27 @ k1_xboole_0)),
% 0.76/1.00      inference('simplify', [status(thm)], ['57'])).
% 0.76/1.00  thf('59', plain,
% 0.76/1.00      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ k1_xboole_0))
% 0.76/1.00         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('demod', [status(thm)], ['56', '58'])).
% 0.76/1.00  thf('60', plain,
% 0.76/1.00      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 0.76/1.00         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('demod', [status(thm)], ['53', '59'])).
% 0.76/1.00  thf('61', plain,
% 0.76/1.00      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('split', [status(esa)], ['26'])).
% 0.76/1.00  thf('62', plain,
% 0.76/1.00      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.76/1.00         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.76/1.00      inference('split', [status(esa)], ['29'])).
% 0.76/1.00  thf('63', plain,
% 0.76/1.00      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 0.76/1.00         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.76/1.00             (((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['61', '62'])).
% 0.76/1.00  thf('64', plain,
% 0.76/1.00      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.76/1.00      inference('sup-', [status(thm)], ['60', '63'])).
% 0.76/1.00  thf('65', plain,
% 0.76/1.00      (((m1_subset_1 @ sk_D @ 
% 0.76/1.00         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 0.76/1.00         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('sup+', [status(thm)], ['44', '45'])).
% 0.76/1.00  thf('66', plain,
% 0.76/1.00      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('split', [status(esa)], ['26'])).
% 0.76/1.00  thf('67', plain,
% 0.76/1.00      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.76/1.00         <= (~
% 0.76/1.00             ((m1_subset_1 @ sk_D @ 
% 0.76/1.00               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.76/1.00      inference('split', [status(esa)], ['29'])).
% 0.76/1.00  thf('68', plain,
% 0.76/1.00      ((~ (m1_subset_1 @ sk_D @ 
% 0.76/1.00           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 0.76/1.00         <= (~
% 0.76/1.00             ((m1_subset_1 @ sk_D @ 
% 0.76/1.00               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 0.76/1.00             (((sk_A) = (k1_xboole_0))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['66', '67'])).
% 0.76/1.00  thf('69', plain,
% 0.76/1.00      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.76/1.00       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['65', '68'])).
% 0.76/1.00  thf('70', plain,
% 0.76/1.00      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 0.76/1.00       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ ((v1_funct_1 @ sk_D))),
% 0.76/1.00      inference('split', [status(esa)], ['29'])).
% 0.76/1.00  thf('71', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.76/1.00      inference('split', [status(esa)], ['26'])).
% 0.76/1.00  thf('72', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.76/1.00      inference('sat_resolution*', [status(thm)],
% 0.76/1.00                ['31', '64', '69', '70', '71'])).
% 0.76/1.00  thf('73', plain, (((sk_B) != (k1_xboole_0))),
% 0.76/1.00      inference('simpl_trail', [status(thm)], ['27', '72'])).
% 0.76/1.00  thf('74', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.76/1.00      inference('simplify_reflect-', [status(thm)], ['25', '73'])).
% 0.76/1.00  thf('75', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.76/1.00      inference('demod', [status(thm)], ['20', '74'])).
% 0.76/1.00  thf('76', plain,
% 0.76/1.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.76/1.00      inference('demod', [status(thm)], ['13', '75'])).
% 0.76/1.00  thf('77', plain,
% 0.76/1.00      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.76/1.00         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.76/1.00          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.76/1.00          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/1.00  thf('78', plain,
% 0.76/1.00      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 0.76/1.00        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_A))),
% 0.76/1.00      inference('sup-', [status(thm)], ['76', '77'])).
% 0.76/1.00  thf('79', plain,
% 0.76/1.00      ((m1_subset_1 @ sk_D @ 
% 0.76/1.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C_1)))),
% 0.76/1.00      inference('demod', [status(thm)], ['9', '12'])).
% 0.76/1.00  thf('80', plain,
% 0.76/1.00      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.76/1.00         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.76/1.00          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.76/1.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/1.00  thf('81', plain,
% 0.76/1.00      (((k1_relset_1 @ (k1_relat_1 @ sk_D) @ sk_C_1 @ sk_D)
% 0.76/1.00         = (k1_relat_1 @ sk_D))),
% 0.76/1.00      inference('sup-', [status(thm)], ['79', '80'])).
% 0.76/1.00  thf('82', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.76/1.00      inference('demod', [status(thm)], ['20', '74'])).
% 0.76/1.00  thf('83', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.76/1.00      inference('demod', [status(thm)], ['20', '74'])).
% 0.76/1.00  thf('84', plain, (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (sk_A))),
% 0.76/1.00      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.76/1.00  thf('85', plain,
% 0.76/1.00      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.76/1.00         (((X29) != (k1_relset_1 @ X29 @ X30 @ X31))
% 0.76/1.00          | (v1_funct_2 @ X31 @ X29 @ X30)
% 0.76/1.00          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/1.00  thf('86', plain,
% 0.76/1.00      ((((sk_A) != (sk_A))
% 0.76/1.00        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 0.76/1.00        | (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.76/1.00      inference('sup-', [status(thm)], ['84', '85'])).
% 0.76/1.00  thf('87', plain,
% 0.76/1.00      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 0.76/1.00        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A))),
% 0.76/1.00      inference('simplify', [status(thm)], ['86'])).
% 0.76/1.00  thf('88', plain,
% 0.76/1.00      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.76/1.00         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.76/1.00      inference('split', [status(esa)], ['29'])).
% 0.76/1.00  thf('89', plain,
% 0.76/1.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.76/1.00      inference('demod', [status(thm)], ['13', '75'])).
% 0.76/1.00  thf('90', plain,
% 0.76/1.00      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.76/1.00         <= (~
% 0.76/1.00             ((m1_subset_1 @ sk_D @ 
% 0.76/1.00               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.76/1.00      inference('split', [status(esa)], ['29'])).
% 0.76/1.00  thf('91', plain,
% 0.76/1.00      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['89', '90'])).
% 0.76/1.00  thf('92', plain,
% 0.76/1.00      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | 
% 0.76/1.00       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 0.76/1.00       ~ ((v1_funct_1 @ sk_D))),
% 0.76/1.00      inference('split', [status(esa)], ['29'])).
% 0.76/1.00  thf('93', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.76/1.00      inference('sat_resolution*', [status(thm)], ['31', '91', '92'])).
% 0.76/1.00  thf('94', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.76/1.00      inference('simpl_trail', [status(thm)], ['88', '93'])).
% 0.76/1.00  thf('95', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)),
% 0.76/1.00      inference('clc', [status(thm)], ['87', '94'])).
% 0.76/1.00  thf('96', plain, (~ (zip_tseitin_0 @ sk_C_1 @ sk_A)),
% 0.76/1.00      inference('clc', [status(thm)], ['78', '95'])).
% 0.76/1.00  thf('97', plain,
% 0.76/1.00      (![X27 : $i, X28 : $i]:
% 0.76/1.00         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/1.00  thf('98', plain, (~ (zip_tseitin_0 @ sk_C_1 @ sk_A)),
% 0.76/1.00      inference('clc', [status(thm)], ['78', '95'])).
% 0.76/1.00  thf('99', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.76/1.00      inference('sup-', [status(thm)], ['97', '98'])).
% 0.76/1.00  thf('100', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A)),
% 0.76/1.00      inference('demod', [status(thm)], ['96', '99'])).
% 0.76/1.00  thf(d3_tarski, axiom,
% 0.76/1.00    (![A:$i,B:$i]:
% 0.76/1.00     ( ( r1_tarski @ A @ B ) <=>
% 0.76/1.00       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.76/1.00  thf('101', plain,
% 0.76/1.00      (![X1 : $i, X3 : $i]:
% 0.76/1.00         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.76/1.00      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/1.00  thf('102', plain,
% 0.76/1.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf(t6_funct_2, axiom,
% 0.76/1.00    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/1.00     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.76/1.00         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/1.00       ( ( r2_hidden @ C @ A ) =>
% 0.76/1.00         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.76/1.00           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.76/1.00  thf('103', plain,
% 0.76/1.00      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.76/1.00         (~ (r2_hidden @ X35 @ X36)
% 0.76/1.00          | ((X37) = (k1_xboole_0))
% 0.76/1.00          | ~ (v1_funct_1 @ X38)
% 0.76/1.00          | ~ (v1_funct_2 @ X38 @ X36 @ X37)
% 0.76/1.00          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.76/1.00          | (r2_hidden @ (k1_funct_1 @ X38 @ X35) @ 
% 0.76/1.00             (k2_relset_1 @ X36 @ X37 @ X38)))),
% 0.76/1.00      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.76/1.00  thf('104', plain,
% 0.76/1.00      (![X0 : $i]:
% 0.76/1.00         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.76/1.00           (k2_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.76/1.00          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.76/1.00          | ~ (v1_funct_1 @ sk_D)
% 0.76/1.00          | ((sk_B) = (k1_xboole_0))
% 0.76/1.00          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.76/1.00      inference('sup-', [status(thm)], ['102', '103'])).
% 0.76/1.00  thf('105', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('106', plain, ((v1_funct_1 @ sk_D)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('107', plain,
% 0.76/1.00      (![X0 : $i]:
% 0.76/1.00         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.76/1.00           (k2_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.76/1.00          | ((sk_B) = (k1_xboole_0))
% 0.76/1.00          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.76/1.00      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.76/1.00  thf('108', plain, (((sk_B) != (k1_xboole_0))),
% 0.76/1.00      inference('simpl_trail', [status(thm)], ['27', '72'])).
% 0.76/1.00  thf('109', plain,
% 0.76/1.00      (![X0 : $i]:
% 0.76/1.00         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.76/1.00           (k2_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.76/1.00          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.76/1.00      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 0.76/1.00  thf('110', plain,
% 0.76/1.00      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_C_1)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('111', plain,
% 0.76/1.00      (![X4 : $i, X6 : $i]:
% 0.76/1.00         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.76/1.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/1.00  thf('112', plain,
% 0.76/1.00      ((~ (r1_tarski @ sk_C_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.76/1.00        | ((sk_C_1) = (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.76/1.00      inference('sup-', [status(thm)], ['110', '111'])).
% 0.76/1.00  thf('113', plain,
% 0.76/1.00      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.76/1.00      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/1.00  thf('114', plain,
% 0.76/1.00      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.76/1.00      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/1.00  thf('115', plain,
% 0.76/1.00      ((~ (r1_tarski @ sk_C_1 @ (k2_relat_1 @ sk_D))
% 0.76/1.00        | ((sk_C_1) = (k2_relat_1 @ sk_D)))),
% 0.76/1.00      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.76/1.00  thf('116', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.76/1.00      inference('sup-', [status(thm)], ['97', '98'])).
% 0.76/1.00  thf('117', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.76/1.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.76/1.00  thf('118', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.76/1.00      inference('sup-', [status(thm)], ['97', '98'])).
% 0.76/1.00  thf('119', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_D))),
% 0.76/1.00      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 0.76/1.00  thf('120', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i]:
% 0.76/1.00         (~ (v1_relat_1 @ X0)
% 0.76/1.00          | (m1_subset_1 @ X0 @ 
% 0.76/1.00             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.76/1.00          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.76/1.00      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/1.00  thf('121', plain,
% 0.76/1.00      (![X0 : $i]:
% 0.76/1.00         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.76/1.00          | (m1_subset_1 @ sk_D @ 
% 0.76/1.00             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)))
% 0.76/1.00          | ~ (v1_relat_1 @ sk_D))),
% 0.76/1.00      inference('sup-', [status(thm)], ['119', '120'])).
% 0.76/1.00  thf('122', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.76/1.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.76/1.00  thf('123', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.76/1.00      inference('demod', [status(thm)], ['20', '74'])).
% 0.76/1.00  thf('124', plain, ((v1_relat_1 @ sk_D)),
% 0.76/1.00      inference('sup-', [status(thm)], ['10', '11'])).
% 0.76/1.00  thf('125', plain,
% 0.76/1.00      (![X0 : $i]:
% 0.76/1.00         (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))),
% 0.76/1.00      inference('demod', [status(thm)], ['121', '122', '123', '124'])).
% 0.76/1.00  thf('126', plain,
% 0.76/1.00      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.76/1.00         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.76/1.00          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.76/1.00      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.76/1.00  thf('127', plain,
% 0.76/1.00      (![X0 : $i]: ((k2_relset_1 @ sk_A @ X0 @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.76/1.00      inference('sup-', [status(thm)], ['125', '126'])).
% 0.76/1.00  thf('128', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_D))),
% 0.76/1.00      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 0.76/1.00  thf('129', plain,
% 0.76/1.00      (![X0 : $i]: ((k2_relset_1 @ sk_A @ X0 @ sk_D) = (k1_xboole_0))),
% 0.76/1.00      inference('demod', [status(thm)], ['127', '128'])).
% 0.76/1.00  thf('130', plain,
% 0.76/1.00      (![X0 : $i]:
% 0.76/1.00         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ k1_xboole_0)
% 0.76/1.00          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.76/1.00      inference('demod', [status(thm)], ['109', '129'])).
% 0.76/1.00  thf('131', plain,
% 0.76/1.00      (![X0 : $i]:
% 0.76/1.00         ((r1_tarski @ sk_A @ X0)
% 0.76/1.00          | (r2_hidden @ (k1_funct_1 @ sk_D @ (sk_C @ X0 @ sk_A)) @ k1_xboole_0))),
% 0.76/1.00      inference('sup-', [status(thm)], ['101', '130'])).
% 0.76/1.00  thf(t7_ordinal1, axiom,
% 0.76/1.00    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/1.00  thf('132', plain,
% 0.76/1.00      (![X10 : $i, X11 : $i]:
% 0.76/1.00         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 0.76/1.00      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.76/1.00  thf('133', plain,
% 0.76/1.00      (![X0 : $i]:
% 0.76/1.00         ((r1_tarski @ sk_A @ X0)
% 0.76/1.00          | ~ (r1_tarski @ k1_xboole_0 @ 
% 0.76/1.00               (k1_funct_1 @ sk_D @ (sk_C @ X0 @ sk_A))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['131', '132'])).
% 0.76/1.00  thf('134', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.76/1.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.76/1.00  thf('135', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.76/1.00      inference('demod', [status(thm)], ['133', '134'])).
% 0.76/1.00  thf('136', plain,
% 0.76/1.00      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.76/1.00      inference('sup-', [status(thm)], ['41', '42'])).
% 0.76/1.00  thf('137', plain, (((sk_A) = (k1_xboole_0))),
% 0.76/1.00      inference('sup-', [status(thm)], ['135', '136'])).
% 0.76/1.00  thf('138', plain,
% 0.76/1.00      (![X27 : $i, X28 : $i]:
% 0.76/1.00         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/1.00  thf('139', plain, (![X27 : $i]: (zip_tseitin_0 @ X27 @ k1_xboole_0)),
% 0.76/1.00      inference('simplify', [status(thm)], ['57'])).
% 0.76/1.00  thf('140', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/1.00         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.76/1.00      inference('sup+', [status(thm)], ['138', '139'])).
% 0.76/1.00  thf('141', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.76/1.00      inference('eq_fact', [status(thm)], ['140'])).
% 0.76/1.00  thf('142', plain, ($false),
% 0.76/1.00      inference('demod', [status(thm)], ['100', '137', '141'])).
% 0.76/1.00  
% 0.76/1.00  % SZS output end Refutation
% 0.76/1.00  
% 0.76/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
