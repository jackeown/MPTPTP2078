%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DqndI6i669

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:11 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  151 (1753 expanded)
%              Number of leaves         :   35 ( 516 expanded)
%              Depth                    :   30
%              Number of atoms          : 1085 (23918 expanded)
%              Number of equality atoms :   82 (1413 expanded)
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

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t218_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v5_relat_1 @ C @ A ) )
         => ( v5_relat_1 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v5_relat_1 @ X8 @ X9 )
      | ( v5_relat_1 @ X8 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t218_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ X0 @ sk_C )
      | ~ ( v5_relat_1 @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v5_relat_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v5_relat_1 @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['13','16'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['14','15'])).

thf('21',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X22 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['14','15'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('30',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
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
    inference(demod,[status(thm)],['19','20'])).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('52',plain,
    ( ( v4_relat_1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v4_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('54',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['14','15'])).

thf('56',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('58',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

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
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('62',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['14','15'])).

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
    inference('sup-',[status(thm)],['47','63'])).

thf('65',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ X0 @ sk_C @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ X0 @ sk_C @ sk_D )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ X0 )
        | ( v1_funct_2 @ sk_D @ X0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
      | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('73',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','63'])).

thf('75',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_1 @ sk_D @ sk_C @ X0 )
        | ~ ( zip_tseitin_0 @ sk_C @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','77'])).

thf('79',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('80',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['44'])).

thf('81',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','63'])).

thf('84',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['44'])).

thf('85',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['44'])).

thf('87',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('88',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['46','82','85','86','87'])).

thf('89',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['42','88'])).

thf('90',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['40','89'])).

thf('91',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['35','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','91'])).

thf('93',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('94',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','91'])).

thf('96',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('97',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['35','90'])).

thf('99',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('101',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['44'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','91'])).

thf('105',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['44'])).

thf('106',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['44'])).

thf('108',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['46','106','107'])).

thf('109',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['103','108'])).

thf('110',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['102','109'])).

thf('111',plain,(
    ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['94','110'])).

thf('112',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','111'])).

thf('113',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['42','88'])).

thf('114',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['112','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DqndI6i669
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:40:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.67  % Solved by: fo/fo7.sh
% 0.47/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.67  % done 251 iterations in 0.205s
% 0.47/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.67  % SZS output start Refutation
% 0.47/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.47/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.47/0.67  thf(t9_funct_2, conjecture,
% 0.47/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.67       ( ( r1_tarski @ B @ C ) =>
% 0.47/0.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.67           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.47/0.67             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.67            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.67          ( ( r1_tarski @ B @ C ) =>
% 0.47/0.67            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.67              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.47/0.67                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.47/0.67    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.47/0.67  thf('0', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(d1_funct_2, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.47/0.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.47/0.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.47/0.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_1, axiom,
% 0.47/0.67    (![B:$i,A:$i]:
% 0.47/0.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.67       ( zip_tseitin_0 @ B @ A ) ))).
% 0.47/0.67  thf('1', plain,
% 0.47/0.67      (![X23 : $i, X24 : $i]:
% 0.47/0.67         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.67  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.67  thf('2', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.47/0.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.67  thf(d10_xboole_0, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.67  thf('3', plain,
% 0.47/0.67      (![X0 : $i, X2 : $i]:
% 0.47/0.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.67  thf('4', plain,
% 0.47/0.67      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.67  thf('5', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         (~ (r1_tarski @ X1 @ X0)
% 0.47/0.67          | (zip_tseitin_0 @ X0 @ X2)
% 0.47/0.67          | ((X1) = (k1_xboole_0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['1', '4'])).
% 0.47/0.67  thf('6', plain,
% 0.47/0.67      (![X0 : $i]: (((sk_B) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_C @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['0', '5'])).
% 0.47/0.67  thf('7', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(cc2_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.67  thf('8', plain,
% 0.47/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.67         ((v5_relat_1 @ X14 @ X16)
% 0.47/0.67          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.67  thf('9', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.47/0.67      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.67  thf('10', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(t218_relat_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( r1_tarski @ A @ B ) =>
% 0.47/0.67       ( ![C:$i]:
% 0.47/0.67         ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) ) =>
% 0.47/0.67           ( v5_relat_1 @ C @ B ) ) ) ))).
% 0.47/0.67  thf('11', plain,
% 0.47/0.67      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X8)
% 0.47/0.67          | ~ (v5_relat_1 @ X8 @ X9)
% 0.47/0.67          | (v5_relat_1 @ X8 @ X10)
% 0.47/0.67          | ~ (r1_tarski @ X9 @ X10))),
% 0.47/0.67      inference('cnf', [status(esa)], [t218_relat_1])).
% 0.47/0.67  thf('12', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((v5_relat_1 @ X0 @ sk_C)
% 0.47/0.67          | ~ (v5_relat_1 @ X0 @ sk_B)
% 0.47/0.67          | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.67  thf('13', plain, ((~ (v1_relat_1 @ sk_D) | (v5_relat_1 @ sk_D @ sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['9', '12'])).
% 0.47/0.67  thf('14', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(cc1_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( v1_relat_1 @ C ) ))).
% 0.47/0.67  thf('15', plain,
% 0.47/0.67      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.67         ((v1_relat_1 @ X11)
% 0.47/0.67          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.67  thf('16', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.67  thf('17', plain, ((v5_relat_1 @ sk_D @ sk_C)),
% 0.47/0.67      inference('demod', [status(thm)], ['13', '16'])).
% 0.47/0.67  thf(d19_relat_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ B ) =>
% 0.47/0.67       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.67  thf('18', plain,
% 0.47/0.67      (![X6 : $i, X7 : $i]:
% 0.47/0.67         (~ (v5_relat_1 @ X6 @ X7)
% 0.47/0.67          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.47/0.67          | ~ (v1_relat_1 @ X6))),
% 0.47/0.67      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.47/0.67  thf('19', plain,
% 0.47/0.67      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.67  thf('20', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.67  thf('21', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.47/0.67      inference('demod', [status(thm)], ['19', '20'])).
% 0.47/0.67  thf('22', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.47/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.67  thf('23', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.47/0.67      inference('simplify', [status(thm)], ['22'])).
% 0.47/0.67  thf(t11_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ C ) =>
% 0.47/0.67       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.47/0.67           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.47/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.47/0.67  thf('24', plain,
% 0.47/0.67      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.67         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.47/0.67          | ~ (r1_tarski @ (k2_relat_1 @ X20) @ X22)
% 0.47/0.67          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.47/0.67          | ~ (v1_relat_1 @ X20))),
% 0.47/0.67      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.47/0.67  thf('25', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | (m1_subset_1 @ X0 @ 
% 0.47/0.67             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.47/0.67          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.47/0.67      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.67  thf('26', plain,
% 0.47/0.67      (((m1_subset_1 @ sk_D @ 
% 0.47/0.67         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))
% 0.47/0.67        | ~ (v1_relat_1 @ sk_D))),
% 0.47/0.67      inference('sup-', [status(thm)], ['21', '25'])).
% 0.47/0.67  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.67  thf('28', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 0.47/0.67      inference('demod', [status(thm)], ['26', '27'])).
% 0.47/0.67  thf('29', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(zf_stmt_2, axiom,
% 0.47/0.67    (![C:$i,B:$i,A:$i]:
% 0.47/0.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.47/0.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.67  thf('30', plain,
% 0.47/0.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.67         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.47/0.67          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.47/0.67          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.67  thf('31', plain,
% 0.47/0.67      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.47/0.67        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.67  thf('32', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.67  thf('33', plain,
% 0.47/0.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.67         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.47/0.67          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.67  thf('34', plain,
% 0.47/0.67      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.47/0.67      inference('sup-', [status(thm)], ['32', '33'])).
% 0.47/0.67  thf('35', plain,
% 0.47/0.67      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.47/0.67      inference('demod', [status(thm)], ['31', '34'])).
% 0.47/0.67  thf('36', plain,
% 0.47/0.67      (![X23 : $i, X24 : $i]:
% 0.47/0.67         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.67  thf('37', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.47/0.67  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.47/0.67  thf(zf_stmt_5, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.47/0.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.47/0.67  thf('38', plain,
% 0.47/0.67      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.47/0.67         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.47/0.67          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.47/0.67          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.67  thf('39', plain,
% 0.47/0.67      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.67  thf('40', plain,
% 0.47/0.67      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['36', '39'])).
% 0.47/0.67  thf('41', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('42', plain,
% 0.47/0.67      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.47/0.67      inference('split', [status(esa)], ['41'])).
% 0.47/0.67  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('44', plain,
% 0.47/0.67      ((~ (v1_funct_1 @ sk_D)
% 0.47/0.67        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.47/0.67        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('45', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.47/0.67      inference('split', [status(esa)], ['44'])).
% 0.47/0.67  thf('46', plain, (((v1_funct_1 @ sk_D))),
% 0.47/0.67      inference('sup-', [status(thm)], ['43', '45'])).
% 0.47/0.67  thf('47', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.47/0.67      inference('demod', [status(thm)], ['19', '20'])).
% 0.47/0.67  thf('48', plain,
% 0.47/0.67      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('split', [status(esa)], ['41'])).
% 0.47/0.67  thf('49', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('50', plain,
% 0.47/0.67      (((m1_subset_1 @ sk_D @ 
% 0.47/0.67         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.47/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup+', [status(thm)], ['48', '49'])).
% 0.47/0.67  thf('51', plain,
% 0.47/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.67         ((v4_relat_1 @ X14 @ X15)
% 0.47/0.67          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.67  thf('52', plain,
% 0.47/0.67      (((v4_relat_1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.67  thf(d18_relat_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ B ) =>
% 0.47/0.67       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.67  thf('53', plain,
% 0.47/0.67      (![X4 : $i, X5 : $i]:
% 0.47/0.67         (~ (v4_relat_1 @ X4 @ X5)
% 0.47/0.67          | (r1_tarski @ (k1_relat_1 @ X4) @ X5)
% 0.47/0.67          | ~ (v1_relat_1 @ X4))),
% 0.47/0.67      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.67  thf('54', plain,
% 0.47/0.67      (((~ (v1_relat_1 @ sk_D)
% 0.47/0.67         | (r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0)))
% 0.47/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['52', '53'])).
% 0.47/0.67  thf('55', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.67  thf('56', plain,
% 0.47/0.67      (((r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0))
% 0.47/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['54', '55'])).
% 0.47/0.67  thf('57', plain,
% 0.47/0.67      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.67  thf('58', plain,
% 0.47/0.67      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['56', '57'])).
% 0.47/0.67  thf('59', plain,
% 0.47/0.67      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.67         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.47/0.67          | ~ (r1_tarski @ (k2_relat_1 @ X20) @ X22)
% 0.47/0.67          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.47/0.67          | ~ (v1_relat_1 @ X20))),
% 0.47/0.67      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.47/0.67  thf('60', plain,
% 0.47/0.67      ((![X0 : $i, X1 : $i]:
% 0.47/0.67          (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.47/0.67           | ~ (v1_relat_1 @ sk_D)
% 0.47/0.67           | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.47/0.67           | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X1)))
% 0.47/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['58', '59'])).
% 0.47/0.67  thf('61', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.47/0.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.67  thf('62', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.67  thf('63', plain,
% 0.47/0.67      ((![X0 : $i, X1 : $i]:
% 0.47/0.67          ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.47/0.67           | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X1)))
% 0.47/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.47/0.67  thf('64', plain,
% 0.47/0.67      ((![X0 : $i]:
% 0.47/0.67          (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C))))
% 0.47/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['47', '63'])).
% 0.47/0.67  thf('65', plain,
% 0.47/0.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.67         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.47/0.67          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.67  thf('66', plain,
% 0.47/0.67      ((![X0 : $i]: ((k1_relset_1 @ X0 @ sk_C @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.47/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['64', '65'])).
% 0.47/0.67  thf('67', plain,
% 0.47/0.67      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['56', '57'])).
% 0.47/0.67  thf('68', plain,
% 0.47/0.67      ((![X0 : $i]: ((k1_relset_1 @ X0 @ sk_C @ sk_D) = (k1_xboole_0)))
% 0.47/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['66', '67'])).
% 0.47/0.67  thf('69', plain,
% 0.47/0.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.67         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 0.47/0.67          | (v1_funct_2 @ X27 @ X25 @ X26)
% 0.47/0.67          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.67  thf('70', plain,
% 0.47/0.67      ((![X0 : $i]:
% 0.47/0.67          (((X0) != (k1_xboole_0))
% 0.47/0.67           | ~ (zip_tseitin_1 @ sk_D @ sk_C @ X0)
% 0.47/0.67           | (v1_funct_2 @ sk_D @ X0 @ sk_C)))
% 0.47/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['68', '69'])).
% 0.47/0.67  thf('71', plain,
% 0.47/0.67      ((((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C)
% 0.47/0.67         | ~ (zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0)))
% 0.47/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('simplify', [status(thm)], ['70'])).
% 0.47/0.67  thf('72', plain,
% 0.47/0.67      (![X23 : $i, X24 : $i]:
% 0.47/0.67         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.67  thf('73', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 0.47/0.67      inference('simplify', [status(thm)], ['72'])).
% 0.47/0.67  thf('74', plain,
% 0.47/0.67      ((![X0 : $i]:
% 0.47/0.67          (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C))))
% 0.47/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['47', '63'])).
% 0.47/0.67  thf('75', plain,
% 0.47/0.67      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.47/0.67         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.47/0.67          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.47/0.67          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.67  thf('76', plain,
% 0.47/0.67      ((![X0 : $i]:
% 0.47/0.67          ((zip_tseitin_1 @ sk_D @ sk_C @ X0) | ~ (zip_tseitin_0 @ sk_C @ X0)))
% 0.47/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['74', '75'])).
% 0.47/0.67  thf('77', plain,
% 0.47/0.67      (((zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0))
% 0.47/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['73', '76'])).
% 0.47/0.67  thf('78', plain,
% 0.47/0.67      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.47/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['71', '77'])).
% 0.47/0.67  thf('79', plain,
% 0.47/0.67      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('split', [status(esa)], ['41'])).
% 0.47/0.67  thf('80', plain,
% 0.47/0.67      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.47/0.67         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.47/0.67      inference('split', [status(esa)], ['44'])).
% 0.47/0.67  thf('81', plain,
% 0.47/0.67      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.47/0.67         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['79', '80'])).
% 0.47/0.67  thf('82', plain,
% 0.47/0.67      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['78', '81'])).
% 0.47/0.67  thf('83', plain,
% 0.47/0.67      ((![X0 : $i]:
% 0.47/0.67          (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C))))
% 0.47/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['47', '63'])).
% 0.47/0.67  thf('84', plain,
% 0.47/0.67      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.47/0.67         <= (~
% 0.47/0.67             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.47/0.67      inference('split', [status(esa)], ['44'])).
% 0.47/0.67  thf('85', plain,
% 0.47/0.67      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.47/0.67       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['83', '84'])).
% 0.47/0.67  thf('86', plain,
% 0.47/0.67      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.47/0.67       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 0.47/0.67      inference('split', [status(esa)], ['44'])).
% 0.47/0.67  thf('87', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.47/0.67      inference('split', [status(esa)], ['41'])).
% 0.47/0.67  thf('88', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.47/0.67      inference('sat_resolution*', [status(thm)],
% 0.47/0.67                ['46', '82', '85', '86', '87'])).
% 0.47/0.67  thf('89', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.67      inference('simpl_trail', [status(thm)], ['42', '88'])).
% 0.47/0.67  thf('90', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['40', '89'])).
% 0.47/0.67  thf('91', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.47/0.67      inference('demod', [status(thm)], ['35', '90'])).
% 0.47/0.67  thf('92', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.47/0.67      inference('demod', [status(thm)], ['28', '91'])).
% 0.47/0.67  thf('93', plain,
% 0.47/0.67      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.47/0.67         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.47/0.67          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.47/0.67          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.67  thf('94', plain,
% 0.47/0.67      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['92', '93'])).
% 0.47/0.67  thf('95', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.47/0.67      inference('demod', [status(thm)], ['28', '91'])).
% 0.47/0.67  thf('96', plain,
% 0.47/0.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.67         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.47/0.67          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.67  thf('97', plain,
% 0.47/0.67      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.47/0.67      inference('sup-', [status(thm)], ['95', '96'])).
% 0.47/0.67  thf('98', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.47/0.67      inference('demod', [status(thm)], ['35', '90'])).
% 0.47/0.67  thf('99', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['97', '98'])).
% 0.47/0.67  thf('100', plain,
% 0.47/0.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.67         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 0.47/0.67          | (v1_funct_2 @ X27 @ X25 @ X26)
% 0.47/0.67          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.67  thf('101', plain,
% 0.47/0.67      ((((sk_A) != (sk_A))
% 0.47/0.67        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.47/0.67        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['99', '100'])).
% 0.47/0.67  thf('102', plain,
% 0.47/0.67      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.47/0.67        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.47/0.67      inference('simplify', [status(thm)], ['101'])).
% 0.47/0.67  thf('103', plain,
% 0.47/0.67      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.47/0.67         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.47/0.67      inference('split', [status(esa)], ['44'])).
% 0.47/0.67  thf('104', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.47/0.67      inference('demod', [status(thm)], ['28', '91'])).
% 0.47/0.67  thf('105', plain,
% 0.47/0.67      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.47/0.67         <= (~
% 0.47/0.67             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.47/0.67      inference('split', [status(esa)], ['44'])).
% 0.47/0.67  thf('106', plain,
% 0.47/0.67      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['104', '105'])).
% 0.47/0.67  thf('107', plain,
% 0.47/0.67      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.47/0.67       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.47/0.67       ~ ((v1_funct_1 @ sk_D))),
% 0.47/0.67      inference('split', [status(esa)], ['44'])).
% 0.47/0.67  thf('108', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.47/0.67      inference('sat_resolution*', [status(thm)], ['46', '106', '107'])).
% 0.47/0.67  thf('109', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.47/0.67      inference('simpl_trail', [status(thm)], ['103', '108'])).
% 0.47/0.67  thf('110', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 0.47/0.67      inference('clc', [status(thm)], ['102', '109'])).
% 0.47/0.67  thf('111', plain, (~ (zip_tseitin_0 @ sk_C @ sk_A)),
% 0.47/0.67      inference('clc', [status(thm)], ['94', '110'])).
% 0.47/0.67  thf('112', plain, (((sk_B) = (k1_xboole_0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['6', '111'])).
% 0.47/0.67  thf('113', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.67      inference('simpl_trail', [status(thm)], ['42', '88'])).
% 0.47/0.67  thf('114', plain, ($false),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['112', '113'])).
% 0.47/0.67  
% 0.47/0.67  % SZS output end Refutation
% 0.47/0.67  
% 0.47/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
