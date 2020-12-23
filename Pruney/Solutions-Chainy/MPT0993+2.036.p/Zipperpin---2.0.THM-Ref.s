%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7JO6di71Ib

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:50 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 147 expanded)
%              Number of leaves         :   37 (  59 expanded)
%              Depth                    :   17
%              Number of atoms          :  685 (1610 expanded)
%              Number of equality atoms :   45 (  57 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ( ( k2_partfun1 @ X35 @ X36 @ X34 @ X37 )
        = ( k7_relat_1 @ X34 @ X37 ) ) ) ),
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

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( v4_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('31',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('38',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('42',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('44',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('45',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['10','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','48'])).

thf('50',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('51',plain,(
    v4_relat_1 @ sk_D @ sk_C ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('55',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['43','45'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['6','55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7JO6di71Ib
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.53/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.74  % Solved by: fo/fo7.sh
% 0.53/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.74  % done 273 iterations in 0.286s
% 0.53/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.74  % SZS output start Refutation
% 0.53/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.53/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.53/0.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.53/0.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.53/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.53/0.74  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.53/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.53/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.74  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.53/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.74  thf(sk_D_type, type, sk_D: $i).
% 0.53/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.74  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.53/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.74  thf(t40_funct_2, conjecture,
% 0.53/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.74     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.53/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.74       ( ( r1_tarski @ A @ C ) =>
% 0.53/0.74         ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ))).
% 0.53/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.74    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.74        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.53/0.74            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.74          ( ( r1_tarski @ A @ C ) =>
% 0.53/0.74            ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )),
% 0.53/0.74    inference('cnf.neg', [status(esa)], [t40_funct_2])).
% 0.53/0.74  thf('0', plain,
% 0.53/0.74      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.53/0.74          (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_D)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('1', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(redefinition_k2_partfun1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.74     ( ( ( v1_funct_1 @ C ) & 
% 0.53/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.74       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.53/0.74  thf('2', plain,
% 0.53/0.74      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.53/0.74          | ~ (v1_funct_1 @ X34)
% 0.53/0.74          | ((k2_partfun1 @ X35 @ X36 @ X34 @ X37) = (k7_relat_1 @ X34 @ X37)))),
% 0.53/0.74      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.53/0.74  thf('3', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 0.53/0.74          | ~ (v1_funct_1 @ sk_D))),
% 0.53/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.74  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('5', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['3', '4'])).
% 0.53/0.74  thf('6', plain,
% 0.53/0.74      (~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.53/0.74      inference('demod', [status(thm)], ['0', '5'])).
% 0.53/0.74  thf('7', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('8', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(t13_relset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.53/0.74       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.53/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.53/0.74  thf('9', plain,
% 0.53/0.74      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.53/0.74         (~ (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 0.53/0.74          | (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.53/0.74          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.53/0.74      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.53/0.74  thf('10', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.53/0.74          | ~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.74  thf(d1_funct_2, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.53/0.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.53/0.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.53/0.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.53/0.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.53/0.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.53/0.74  thf(zf_stmt_1, axiom,
% 0.53/0.74    (![B:$i,A:$i]:
% 0.53/0.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.53/0.74       ( zip_tseitin_0 @ B @ A ) ))).
% 0.53/0.74  thf('11', plain,
% 0.53/0.74      (![X26 : $i, X27 : $i]:
% 0.53/0.74         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.53/0.74  thf(t113_zfmisc_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.53/0.74       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.53/0.74  thf('12', plain,
% 0.53/0.74      (![X4 : $i, X5 : $i]:
% 0.53/0.74         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.53/0.74  thf('13', plain,
% 0.53/0.74      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['12'])).
% 0.53/0.74  thf('14', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.53/0.74      inference('sup+', [status(thm)], ['11', '13'])).
% 0.53/0.74  thf('15', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('16', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.53/0.74          | (zip_tseitin_0 @ sk_B @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['14', '15'])).
% 0.53/0.74  thf('17', plain,
% 0.53/0.74      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['12'])).
% 0.53/0.74  thf(cc2_relset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.74       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.53/0.74  thf('18', plain,
% 0.53/0.74      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.53/0.74         ((v4_relat_1 @ X12 @ X13)
% 0.53/0.74          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.53/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.53/0.74  thf('19', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.53/0.74          | (v4_relat_1 @ X1 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['17', '18'])).
% 0.53/0.74  thf('20', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((zip_tseitin_0 @ sk_B @ X1) | (v4_relat_1 @ sk_D @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['16', '19'])).
% 0.53/0.74  thf(t209_relat_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.53/0.74       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.53/0.74  thf('21', plain,
% 0.53/0.74      (![X10 : $i, X11 : $i]:
% 0.53/0.74         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.53/0.74          | ~ (v4_relat_1 @ X10 @ X11)
% 0.53/0.74          | ~ (v1_relat_1 @ X10))),
% 0.53/0.74      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.53/0.74  thf('22', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((zip_tseitin_0 @ sk_B @ X1)
% 0.53/0.74          | ~ (v1_relat_1 @ sk_D)
% 0.53/0.74          | ((sk_D) = (k7_relat_1 @ sk_D @ X0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['20', '21'])).
% 0.53/0.74  thf('23', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(cc2_relat_1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( v1_relat_1 @ A ) =>
% 0.53/0.74       ( ![B:$i]:
% 0.53/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.53/0.74  thf('24', plain,
% 0.53/0.74      (![X6 : $i, X7 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.53/0.74          | (v1_relat_1 @ X6)
% 0.53/0.74          | ~ (v1_relat_1 @ X7))),
% 0.53/0.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.53/0.74  thf('25', plain,
% 0.53/0.74      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.53/0.74      inference('sup-', [status(thm)], ['23', '24'])).
% 0.53/0.74  thf(fc6_relat_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.53/0.74  thf('26', plain,
% 0.53/0.74      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.53/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.53/0.74  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.53/0.74      inference('demod', [status(thm)], ['25', '26'])).
% 0.53/0.74  thf('28', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((zip_tseitin_0 @ sk_B @ X1) | ((sk_D) = (k7_relat_1 @ sk_D @ X0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['22', '27'])).
% 0.53/0.74  thf('29', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.53/0.74  thf(zf_stmt_3, axiom,
% 0.53/0.74    (![C:$i,B:$i,A:$i]:
% 0.53/0.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.53/0.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.53/0.74  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.53/0.74  thf(zf_stmt_5, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.53/0.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.53/0.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.53/0.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.53/0.74  thf('30', plain,
% 0.53/0.74      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.53/0.74         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.53/0.74          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.53/0.74          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.53/0.74  thf('31', plain,
% 0.53/0.74      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['29', '30'])).
% 0.53/0.74  thf('32', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (((sk_D) = (k7_relat_1 @ sk_D @ X0))
% 0.53/0.74          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['28', '31'])).
% 0.53/0.74  thf('33', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('34', plain,
% 0.53/0.74      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.53/0.74         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.53/0.74          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.53/0.74          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.53/0.74  thf('35', plain,
% 0.53/0.74      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.53/0.74        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.53/0.74  thf('36', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(redefinition_k1_relset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.53/0.74  thf('37', plain,
% 0.53/0.74      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.53/0.74         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.53/0.74          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.53/0.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.53/0.74  thf('38', plain,
% 0.53/0.74      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.53/0.74      inference('sup-', [status(thm)], ['36', '37'])).
% 0.53/0.74  thf('39', plain,
% 0.53/0.74      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.53/0.74      inference('demod', [status(thm)], ['35', '38'])).
% 0.53/0.74  thf('40', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (((sk_D) = (k7_relat_1 @ sk_D @ X0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['32', '39'])).
% 0.53/0.74  thf('41', plain,
% 0.53/0.74      (~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.53/0.74      inference('demod', [status(thm)], ['0', '5'])).
% 0.53/0.74  thf('42', plain,
% 0.53/0.74      ((~ (r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)
% 0.53/0.74        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['40', '41'])).
% 0.53/0.74  thf('43', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(redefinition_r2_relset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.74     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.53/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.74       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.53/0.74  thf('44', plain,
% 0.53/0.74      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.53/0.74          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.53/0.74          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 0.53/0.74          | ((X18) != (X21)))),
% 0.53/0.74      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.53/0.74  thf('45', plain,
% 0.53/0.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.53/0.74         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 0.53/0.74          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.53/0.74      inference('simplify', [status(thm)], ['44'])).
% 0.53/0.74  thf('46', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.53/0.74      inference('sup-', [status(thm)], ['43', '45'])).
% 0.53/0.74  thf('47', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.53/0.74      inference('demod', [status(thm)], ['42', '46'])).
% 0.53/0.74  thf('48', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.53/0.74          | ~ (r1_tarski @ sk_A @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['10', '47'])).
% 0.53/0.74  thf('49', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['7', '48'])).
% 0.53/0.74  thf('50', plain,
% 0.53/0.74      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.53/0.74         ((v4_relat_1 @ X12 @ X13)
% 0.53/0.74          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.53/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.53/0.74  thf('51', plain, ((v4_relat_1 @ sk_D @ sk_C)),
% 0.53/0.74      inference('sup-', [status(thm)], ['49', '50'])).
% 0.53/0.74  thf('52', plain,
% 0.53/0.74      (![X10 : $i, X11 : $i]:
% 0.53/0.74         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.53/0.74          | ~ (v4_relat_1 @ X10 @ X11)
% 0.53/0.74          | ~ (v1_relat_1 @ X10))),
% 0.53/0.74      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.53/0.74  thf('53', plain,
% 0.53/0.74      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_C)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['51', '52'])).
% 0.53/0.74  thf('54', plain, ((v1_relat_1 @ sk_D)),
% 0.53/0.74      inference('demod', [status(thm)], ['25', '26'])).
% 0.53/0.74  thf('55', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_C))),
% 0.53/0.74      inference('demod', [status(thm)], ['53', '54'])).
% 0.53/0.74  thf('56', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.53/0.74      inference('sup-', [status(thm)], ['43', '45'])).
% 0.53/0.74  thf('57', plain, ($false),
% 0.53/0.74      inference('demod', [status(thm)], ['6', '55', '56'])).
% 0.53/0.74  
% 0.53/0.74  % SZS output end Refutation
% 0.53/0.74  
% 0.53/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
