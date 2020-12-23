%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ap4AAjm2Rz

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:33 EST 2020

% Result     : Theorem 14.69s
% Output     : Refutation 14.69s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 367 expanded)
%              Number of leaves         :   48 ( 127 expanded)
%              Depth                    :   22
%              Number of atoms          : 1588 (6012 expanded)
%              Number of equality atoms :   86 ( 219 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t37_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ? [D: $i] :
              ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
              & ( v1_funct_2 @ D @ B @ A )
              & ( v1_funct_1 @ D ) )
          & ~ ( v2_funct_1 @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ? [D: $i] :
                ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
                & ( v1_funct_2 @ D @ B @ A )
                & ( v1_funct_1 @ D ) )
            & ~ ( v2_funct_1 @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('13',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C )
      = ( k5_relat_1 @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C )
    = ( k5_relat_1 @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['17','18'])).

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

thf('20',plain,(
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

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('22',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('25',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('33',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ( sk_B
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('38',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    r1_tarski @ ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_tarski @ ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C ) @ k1_xboole_0 )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['35','46'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('49',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k5_relat_1 @ sk_C @ sk_C )
      = k1_xboole_0 )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['19','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('57',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('59',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_D ) )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('63',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_relat_1 @ sk_D ) )
      | ( v5_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_relat_1 @ sk_D ) )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('72',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('75',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('80',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','83'])).

thf(t47_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) )
           => ( v2_funct_1 @ B ) ) ) ) )).

thf('85',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v2_funct_1 @ X13 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_C ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_A )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_C ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['69','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_C ) )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( v2_funct_1 @ k1_xboole_0 )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['50','95'])).

thf('97',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('98',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['97'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('99',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('100',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('101',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('104',plain,(
    r1_tarski @ ( k6_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('106',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['104','105'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('107',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('108',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['96','108'])).

thf('110',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v2_funct_1 @ X13 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_D ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('115',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('117',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_B )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_D ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','117','118'])).

thf('120',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('128',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('131',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['128','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('137',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('141',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('142',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','143'])).

thf('145',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('146',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('148',plain,(
    $false ),
    inference(demod,[status(thm)],['125','146','147'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ap4AAjm2Rz
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 14.69/14.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.69/14.88  % Solved by: fo/fo7.sh
% 14.69/14.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.69/14.88  % done 11022 iterations in 14.439s
% 14.69/14.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.69/14.88  % SZS output start Refutation
% 14.69/14.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 14.69/14.88  thf(sk_B_type, type, sk_B: $i).
% 14.69/14.88  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 14.69/14.88  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 14.69/14.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 14.69/14.88  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 14.69/14.88  thf(sk_D_type, type, sk_D: $i).
% 14.69/14.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 14.69/14.88  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 14.69/14.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 14.69/14.88  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 14.69/14.88  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 14.69/14.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 14.69/14.88  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 14.69/14.88  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 14.69/14.88  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 14.69/14.88  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 14.69/14.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 14.69/14.88  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 14.69/14.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.69/14.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 14.69/14.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 14.69/14.88  thf(sk_A_type, type, sk_A: $i).
% 14.69/14.88  thf(sk_C_type, type, sk_C: $i).
% 14.69/14.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 14.69/14.88  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 14.69/14.88  thf(t37_funct_2, conjecture,
% 14.69/14.88    (![A:$i,B:$i,C:$i]:
% 14.69/14.88     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 14.69/14.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 14.69/14.88       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 14.69/14.88            ( ?[D:$i]:
% 14.69/14.88              ( ( r2_relset_1 @
% 14.69/14.88                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 14.69/14.88                  ( k6_partfun1 @ A ) ) & 
% 14.69/14.88                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 14.69/14.88                ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 14.69/14.88            ( ~( v2_funct_1 @ C ) ) ) ) ))).
% 14.69/14.88  thf(zf_stmt_0, negated_conjecture,
% 14.69/14.88    (~( ![A:$i,B:$i,C:$i]:
% 14.69/14.88        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 14.69/14.88            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 14.69/14.88          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 14.69/14.88               ( ?[D:$i]:
% 14.69/14.88                 ( ( r2_relset_1 @
% 14.69/14.88                     A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 14.69/14.88                     ( k6_partfun1 @ A ) ) & 
% 14.69/14.88                   ( m1_subset_1 @
% 14.69/14.88                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 14.69/14.88                   ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 14.69/14.88               ( ~( v2_funct_1 @ C ) ) ) ) ) )),
% 14.69/14.88    inference('cnf.neg', [status(esa)], [t37_funct_2])).
% 14.69/14.88  thf('0', plain,
% 14.69/14.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf(cc2_relset_1, axiom,
% 14.69/14.88    (![A:$i,B:$i,C:$i]:
% 14.69/14.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.69/14.88       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 14.69/14.88  thf('1', plain,
% 14.69/14.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 14.69/14.88         ((v5_relat_1 @ X16 @ X18)
% 14.69/14.88          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 14.69/14.88      inference('cnf', [status(esa)], [cc2_relset_1])).
% 14.69/14.88  thf('2', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 14.69/14.88      inference('sup-', [status(thm)], ['0', '1'])).
% 14.69/14.88  thf(d19_relat_1, axiom,
% 14.69/14.88    (![A:$i,B:$i]:
% 14.69/14.88     ( ( v1_relat_1 @ B ) =>
% 14.69/14.88       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 14.69/14.88  thf('3', plain,
% 14.69/14.88      (![X9 : $i, X10 : $i]:
% 14.69/14.88         (~ (v5_relat_1 @ X9 @ X10)
% 14.69/14.88          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 14.69/14.88          | ~ (v1_relat_1 @ X9))),
% 14.69/14.88      inference('cnf', [status(esa)], [d19_relat_1])).
% 14.69/14.88  thf('4', plain,
% 14.69/14.88      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 14.69/14.88      inference('sup-', [status(thm)], ['2', '3'])).
% 14.69/14.88  thf('5', plain,
% 14.69/14.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf(cc2_relat_1, axiom,
% 14.69/14.88    (![A:$i]:
% 14.69/14.88     ( ( v1_relat_1 @ A ) =>
% 14.69/14.88       ( ![B:$i]:
% 14.69/14.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 14.69/14.88  thf('6', plain,
% 14.69/14.88      (![X7 : $i, X8 : $i]:
% 14.69/14.88         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 14.69/14.88          | (v1_relat_1 @ X7)
% 14.69/14.88          | ~ (v1_relat_1 @ X8))),
% 14.69/14.88      inference('cnf', [status(esa)], [cc2_relat_1])).
% 14.69/14.88  thf('7', plain,
% 14.69/14.88      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 14.69/14.88      inference('sup-', [status(thm)], ['5', '6'])).
% 14.69/14.88  thf(fc6_relat_1, axiom,
% 14.69/14.88    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 14.69/14.88  thf('8', plain,
% 14.69/14.88      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 14.69/14.88      inference('cnf', [status(esa)], [fc6_relat_1])).
% 14.69/14.88  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 14.69/14.88      inference('demod', [status(thm)], ['7', '8'])).
% 14.69/14.88  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 14.69/14.88      inference('demod', [status(thm)], ['4', '9'])).
% 14.69/14.88  thf('11', plain,
% 14.69/14.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('12', plain,
% 14.69/14.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf(redefinition_k1_partfun1, axiom,
% 14.69/14.88    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 14.69/14.88     ( ( ( v1_funct_1 @ E ) & 
% 14.69/14.88         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 14.69/14.88         ( v1_funct_1 @ F ) & 
% 14.69/14.88         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 14.69/14.88       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 14.69/14.88  thf('13', plain,
% 14.69/14.88      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 14.69/14.88         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 14.69/14.88          | ~ (v1_funct_1 @ X42)
% 14.69/14.88          | ~ (v1_funct_1 @ X45)
% 14.69/14.88          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 14.69/14.88          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 14.69/14.88              = (k5_relat_1 @ X42 @ X45)))),
% 14.69/14.88      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 14.69/14.88  thf('14', plain,
% 14.69/14.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.69/14.88         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 14.69/14.88            = (k5_relat_1 @ sk_C @ X0))
% 14.69/14.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 14.69/14.88          | ~ (v1_funct_1 @ X0)
% 14.69/14.88          | ~ (v1_funct_1 @ sk_C))),
% 14.69/14.88      inference('sup-', [status(thm)], ['12', '13'])).
% 14.69/14.88  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('16', plain,
% 14.69/14.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.69/14.88         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 14.69/14.88            = (k5_relat_1 @ sk_C @ X0))
% 14.69/14.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 14.69/14.88          | ~ (v1_funct_1 @ X0))),
% 14.69/14.88      inference('demod', [status(thm)], ['14', '15'])).
% 14.69/14.88  thf('17', plain,
% 14.69/14.88      ((~ (v1_funct_1 @ sk_C)
% 14.69/14.88        | ((k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C)
% 14.69/14.88            = (k5_relat_1 @ sk_C @ sk_C)))),
% 14.69/14.88      inference('sup-', [status(thm)], ['11', '16'])).
% 14.69/14.88  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('19', plain,
% 14.69/14.88      (((k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C)
% 14.69/14.88         = (k5_relat_1 @ sk_C @ sk_C))),
% 14.69/14.88      inference('demod', [status(thm)], ['17', '18'])).
% 14.69/14.88  thf(d1_funct_2, axiom,
% 14.69/14.88    (![A:$i,B:$i,C:$i]:
% 14.69/14.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.69/14.88       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 14.69/14.88           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 14.69/14.88             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 14.69/14.88         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 14.69/14.88           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 14.69/14.88             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 14.69/14.88  thf(zf_stmt_1, axiom,
% 14.69/14.88    (![B:$i,A:$i]:
% 14.69/14.88     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 14.69/14.88       ( zip_tseitin_0 @ B @ A ) ))).
% 14.69/14.88  thf('20', plain,
% 14.69/14.88      (![X26 : $i, X27 : $i]:
% 14.69/14.88         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_1])).
% 14.69/14.88  thf(t113_zfmisc_1, axiom,
% 14.69/14.88    (![A:$i,B:$i]:
% 14.69/14.88     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 14.69/14.88       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 14.69/14.88  thf('21', plain,
% 14.69/14.88      (![X2 : $i, X3 : $i]:
% 14.69/14.88         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 14.69/14.88      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 14.69/14.88  thf('22', plain,
% 14.69/14.88      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 14.69/14.88      inference('simplify', [status(thm)], ['21'])).
% 14.69/14.88  thf('23', plain,
% 14.69/14.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.69/14.88         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 14.69/14.88      inference('sup+', [status(thm)], ['20', '22'])).
% 14.69/14.88  thf('24', plain,
% 14.69/14.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 14.69/14.88  thf(zf_stmt_3, axiom,
% 14.69/14.88    (![C:$i,B:$i,A:$i]:
% 14.69/14.88     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 14.69/14.88       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 14.69/14.88  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 14.69/14.88  thf(zf_stmt_5, axiom,
% 14.69/14.88    (![A:$i,B:$i,C:$i]:
% 14.69/14.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.69/14.88       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 14.69/14.88         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 14.69/14.88           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 14.69/14.88             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 14.69/14.88  thf('25', plain,
% 14.69/14.88      (![X31 : $i, X32 : $i, X33 : $i]:
% 14.69/14.88         (~ (zip_tseitin_0 @ X31 @ X32)
% 14.69/14.88          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 14.69/14.88          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_5])).
% 14.69/14.88  thf('26', plain,
% 14.69/14.88      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 14.69/14.88      inference('sup-', [status(thm)], ['24', '25'])).
% 14.69/14.88  thf('27', plain,
% 14.69/14.88      (![X0 : $i]:
% 14.69/14.88         (((k2_zfmisc_1 @ sk_A @ X0) = (k1_xboole_0))
% 14.69/14.88          | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 14.69/14.88      inference('sup-', [status(thm)], ['23', '26'])).
% 14.69/14.88  thf('28', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('29', plain,
% 14.69/14.88      (![X28 : $i, X29 : $i, X30 : $i]:
% 14.69/14.88         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 14.69/14.88          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 14.69/14.88          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_3])).
% 14.69/14.88  thf('30', plain,
% 14.69/14.88      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 14.69/14.88        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 14.69/14.88      inference('sup-', [status(thm)], ['28', '29'])).
% 14.69/14.88  thf('31', plain,
% 14.69/14.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf(redefinition_k1_relset_1, axiom,
% 14.69/14.88    (![A:$i,B:$i,C:$i]:
% 14.69/14.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.69/14.88       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 14.69/14.88  thf('32', plain,
% 14.69/14.88      (![X19 : $i, X20 : $i, X21 : $i]:
% 14.69/14.88         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 14.69/14.88          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 14.69/14.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 14.69/14.88  thf('33', plain,
% 14.69/14.88      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 14.69/14.88      inference('sup-', [status(thm)], ['31', '32'])).
% 14.69/14.88  thf('34', plain,
% 14.69/14.88      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 14.69/14.88      inference('demod', [status(thm)], ['30', '33'])).
% 14.69/14.88  thf('35', plain,
% 14.69/14.88      (![X0 : $i]:
% 14.69/14.88         (((k2_zfmisc_1 @ sk_A @ X0) = (k1_xboole_0))
% 14.69/14.88          | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 14.69/14.88      inference('sup-', [status(thm)], ['27', '34'])).
% 14.69/14.88  thf('36', plain,
% 14.69/14.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('37', plain,
% 14.69/14.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf(dt_k1_partfun1, axiom,
% 14.69/14.88    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 14.69/14.88     ( ( ( v1_funct_1 @ E ) & 
% 14.69/14.88         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 14.69/14.88         ( v1_funct_1 @ F ) & 
% 14.69/14.88         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 14.69/14.88       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 14.69/14.88         ( m1_subset_1 @
% 14.69/14.88           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 14.69/14.88           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 14.69/14.88  thf('38', plain,
% 14.69/14.88      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 14.69/14.88         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 14.69/14.88          | ~ (v1_funct_1 @ X34)
% 14.69/14.88          | ~ (v1_funct_1 @ X37)
% 14.69/14.88          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 14.69/14.88          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 14.69/14.88             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 14.69/14.88      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 14.69/14.88  thf('39', plain,
% 14.69/14.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.69/14.88         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 14.69/14.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 14.69/14.88          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 14.69/14.88          | ~ (v1_funct_1 @ X1)
% 14.69/14.88          | ~ (v1_funct_1 @ sk_C))),
% 14.69/14.88      inference('sup-', [status(thm)], ['37', '38'])).
% 14.69/14.88  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('41', plain,
% 14.69/14.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.69/14.88         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 14.69/14.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 14.69/14.88          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 14.69/14.88          | ~ (v1_funct_1 @ X1))),
% 14.69/14.88      inference('demod', [status(thm)], ['39', '40'])).
% 14.69/14.88  thf('42', plain,
% 14.69/14.88      ((~ (v1_funct_1 @ sk_C)
% 14.69/14.88        | (m1_subset_1 @ 
% 14.69/14.88           (k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C) @ 
% 14.69/14.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 14.69/14.88      inference('sup-', [status(thm)], ['36', '41'])).
% 14.69/14.88  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('44', plain,
% 14.69/14.88      ((m1_subset_1 @ 
% 14.69/14.88        (k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C) @ 
% 14.69/14.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.69/14.88      inference('demod', [status(thm)], ['42', '43'])).
% 14.69/14.88  thf(t3_subset, axiom,
% 14.69/14.88    (![A:$i,B:$i]:
% 14.69/14.88     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 14.69/14.88  thf('45', plain,
% 14.69/14.88      (![X4 : $i, X5 : $i]:
% 14.69/14.88         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 14.69/14.88      inference('cnf', [status(esa)], [t3_subset])).
% 14.69/14.88  thf('46', plain,
% 14.69/14.88      ((r1_tarski @ (k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C) @ 
% 14.69/14.88        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 14.69/14.88      inference('sup-', [status(thm)], ['44', '45'])).
% 14.69/14.88  thf('47', plain,
% 14.69/14.88      (((r1_tarski @ (k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C) @ 
% 14.69/14.88         k1_xboole_0)
% 14.69/14.88        | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 14.69/14.88      inference('sup+', [status(thm)], ['35', '46'])).
% 14.69/14.88  thf(t3_xboole_1, axiom,
% 14.69/14.88    (![A:$i]:
% 14.69/14.88     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 14.69/14.88  thf('48', plain,
% 14.69/14.88      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 14.69/14.88      inference('cnf', [status(esa)], [t3_xboole_1])).
% 14.69/14.88  thf('49', plain,
% 14.69/14.88      ((((sk_B) = (k1_relat_1 @ sk_D))
% 14.69/14.88        | ((k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C)
% 14.69/14.88            = (k1_xboole_0)))),
% 14.69/14.88      inference('sup-', [status(thm)], ['47', '48'])).
% 14.69/14.88  thf('50', plain,
% 14.69/14.88      ((((k5_relat_1 @ sk_C @ sk_C) = (k1_xboole_0))
% 14.69/14.88        | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 14.69/14.88      inference('sup+', [status(thm)], ['19', '49'])).
% 14.69/14.88  thf('51', plain,
% 14.69/14.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.69/14.88         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 14.69/14.88      inference('sup+', [status(thm)], ['20', '22'])).
% 14.69/14.88  thf('52', plain,
% 14.69/14.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('53', plain,
% 14.69/14.88      (![X4 : $i, X5 : $i]:
% 14.69/14.88         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 14.69/14.88      inference('cnf', [status(esa)], [t3_subset])).
% 14.69/14.88  thf('54', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 14.69/14.88      inference('sup-', [status(thm)], ['52', '53'])).
% 14.69/14.88  thf('55', plain,
% 14.69/14.88      (![X0 : $i]:
% 14.69/14.88         ((r1_tarski @ sk_C @ k1_xboole_0) | (zip_tseitin_0 @ sk_A @ X0))),
% 14.69/14.88      inference('sup+', [status(thm)], ['51', '54'])).
% 14.69/14.88  thf('56', plain,
% 14.69/14.88      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 14.69/14.88      inference('sup-', [status(thm)], ['24', '25'])).
% 14.69/14.88  thf('57', plain,
% 14.69/14.88      (((r1_tarski @ sk_C @ k1_xboole_0) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 14.69/14.88      inference('sup-', [status(thm)], ['55', '56'])).
% 14.69/14.88  thf('58', plain,
% 14.69/14.88      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 14.69/14.88      inference('demod', [status(thm)], ['30', '33'])).
% 14.69/14.88  thf('59', plain,
% 14.69/14.88      (((r1_tarski @ sk_C @ k1_xboole_0) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 14.69/14.88      inference('sup-', [status(thm)], ['57', '58'])).
% 14.69/14.88  thf('60', plain,
% 14.69/14.88      (![X4 : $i, X6 : $i]:
% 14.69/14.88         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 14.69/14.88      inference('cnf', [status(esa)], [t3_subset])).
% 14.69/14.88  thf('61', plain,
% 14.69/14.88      ((((sk_B) = (k1_relat_1 @ sk_D))
% 14.69/14.88        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 14.69/14.88      inference('sup-', [status(thm)], ['59', '60'])).
% 14.69/14.88  thf('62', plain,
% 14.69/14.88      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 14.69/14.88      inference('simplify', [status(thm)], ['21'])).
% 14.69/14.88  thf('63', plain,
% 14.69/14.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 14.69/14.88         ((v5_relat_1 @ X16 @ X18)
% 14.69/14.88          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 14.69/14.88      inference('cnf', [status(esa)], [cc2_relset_1])).
% 14.69/14.88  thf('64', plain,
% 14.69/14.88      (![X0 : $i, X1 : $i]:
% 14.69/14.88         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 14.69/14.88          | (v5_relat_1 @ X1 @ X0))),
% 14.69/14.88      inference('sup-', [status(thm)], ['62', '63'])).
% 14.69/14.88  thf('65', plain,
% 14.69/14.88      (![X0 : $i]: (((sk_B) = (k1_relat_1 @ sk_D)) | (v5_relat_1 @ sk_C @ X0))),
% 14.69/14.88      inference('sup-', [status(thm)], ['61', '64'])).
% 14.69/14.88  thf('66', plain,
% 14.69/14.88      (![X9 : $i, X10 : $i]:
% 14.69/14.88         (~ (v5_relat_1 @ X9 @ X10)
% 14.69/14.88          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 14.69/14.88          | ~ (v1_relat_1 @ X9))),
% 14.69/14.88      inference('cnf', [status(esa)], [d19_relat_1])).
% 14.69/14.88  thf('67', plain,
% 14.69/14.88      (![X0 : $i]:
% 14.69/14.88         (((sk_B) = (k1_relat_1 @ sk_D))
% 14.69/14.88          | ~ (v1_relat_1 @ sk_C)
% 14.69/14.88          | (r1_tarski @ (k2_relat_1 @ sk_C) @ X0))),
% 14.69/14.88      inference('sup-', [status(thm)], ['65', '66'])).
% 14.69/14.88  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 14.69/14.88      inference('demod', [status(thm)], ['7', '8'])).
% 14.69/14.88  thf('69', plain,
% 14.69/14.88      (![X0 : $i]:
% 14.69/14.88         (((sk_B) = (k1_relat_1 @ sk_D))
% 14.69/14.88          | (r1_tarski @ (k2_relat_1 @ sk_C) @ X0))),
% 14.69/14.88      inference('demod', [status(thm)], ['67', '68'])).
% 14.69/14.88  thf('70', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('71', plain,
% 14.69/14.88      (![X28 : $i, X29 : $i, X30 : $i]:
% 14.69/14.88         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 14.69/14.88          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 14.69/14.88          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_3])).
% 14.69/14.88  thf('72', plain,
% 14.69/14.88      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 14.69/14.88        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 14.69/14.88      inference('sup-', [status(thm)], ['70', '71'])).
% 14.69/14.88  thf('73', plain,
% 14.69/14.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('74', plain,
% 14.69/14.88      (![X19 : $i, X20 : $i, X21 : $i]:
% 14.69/14.88         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 14.69/14.88          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 14.69/14.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 14.69/14.88  thf('75', plain,
% 14.69/14.88      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 14.69/14.88      inference('sup-', [status(thm)], ['73', '74'])).
% 14.69/14.88  thf('76', plain,
% 14.69/14.88      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 14.69/14.88      inference('demod', [status(thm)], ['72', '75'])).
% 14.69/14.88  thf('77', plain,
% 14.69/14.88      (![X26 : $i, X27 : $i]:
% 14.69/14.88         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_1])).
% 14.69/14.88  thf('78', plain,
% 14.69/14.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('79', plain,
% 14.69/14.88      (![X31 : $i, X32 : $i, X33 : $i]:
% 14.69/14.88         (~ (zip_tseitin_0 @ X31 @ X32)
% 14.69/14.88          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 14.69/14.88          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_5])).
% 14.69/14.88  thf('80', plain,
% 14.69/14.88      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 14.69/14.88      inference('sup-', [status(thm)], ['78', '79'])).
% 14.69/14.88  thf('81', plain,
% 14.69/14.88      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 14.69/14.88      inference('sup-', [status(thm)], ['77', '80'])).
% 14.69/14.88  thf('82', plain, (((sk_B) != (k1_xboole_0))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('83', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 14.69/14.88      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 14.69/14.88  thf('84', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 14.69/14.88      inference('demod', [status(thm)], ['76', '83'])).
% 14.69/14.88  thf(t47_funct_1, axiom,
% 14.69/14.88    (![A:$i]:
% 14.69/14.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 14.69/14.88       ( ![B:$i]:
% 14.69/14.88         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 14.69/14.88           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 14.69/14.88               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 14.69/14.88             ( v2_funct_1 @ B ) ) ) ) ))).
% 14.69/14.88  thf('85', plain,
% 14.69/14.88      (![X13 : $i, X14 : $i]:
% 14.69/14.88         (~ (v1_relat_1 @ X13)
% 14.69/14.88          | ~ (v1_funct_1 @ X13)
% 14.69/14.88          | (v2_funct_1 @ X13)
% 14.69/14.88          | ~ (r1_tarski @ (k2_relat_1 @ X13) @ (k1_relat_1 @ X14))
% 14.69/14.88          | ~ (v2_funct_1 @ (k5_relat_1 @ X13 @ X14))
% 14.69/14.88          | ~ (v1_funct_1 @ X14)
% 14.69/14.88          | ~ (v1_relat_1 @ X14))),
% 14.69/14.88      inference('cnf', [status(esa)], [t47_funct_1])).
% 14.69/14.88  thf('86', plain,
% 14.69/14.88      (![X0 : $i]:
% 14.69/14.88         (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_A)
% 14.69/14.88          | ~ (v1_relat_1 @ sk_C)
% 14.69/14.88          | ~ (v1_funct_1 @ sk_C)
% 14.69/14.88          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_C))
% 14.69/14.88          | (v2_funct_1 @ X0)
% 14.69/14.88          | ~ (v1_funct_1 @ X0)
% 14.69/14.88          | ~ (v1_relat_1 @ X0))),
% 14.69/14.88      inference('sup-', [status(thm)], ['84', '85'])).
% 14.69/14.88  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 14.69/14.88      inference('demod', [status(thm)], ['7', '8'])).
% 14.69/14.88  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('89', plain,
% 14.69/14.88      (![X0 : $i]:
% 14.69/14.88         (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_A)
% 14.69/14.88          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_C))
% 14.69/14.88          | (v2_funct_1 @ X0)
% 14.69/14.88          | ~ (v1_funct_1 @ X0)
% 14.69/14.88          | ~ (v1_relat_1 @ X0))),
% 14.69/14.88      inference('demod', [status(thm)], ['86', '87', '88'])).
% 14.69/14.88  thf('90', plain,
% 14.69/14.88      ((((sk_B) = (k1_relat_1 @ sk_D))
% 14.69/14.88        | ~ (v1_relat_1 @ sk_C)
% 14.69/14.88        | ~ (v1_funct_1 @ sk_C)
% 14.69/14.88        | (v2_funct_1 @ sk_C)
% 14.69/14.88        | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_C)))),
% 14.69/14.88      inference('sup-', [status(thm)], ['69', '89'])).
% 14.69/14.88  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 14.69/14.88      inference('demod', [status(thm)], ['7', '8'])).
% 14.69/14.88  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('93', plain,
% 14.69/14.88      ((((sk_B) = (k1_relat_1 @ sk_D))
% 14.69/14.88        | (v2_funct_1 @ sk_C)
% 14.69/14.88        | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_C)))),
% 14.69/14.88      inference('demod', [status(thm)], ['90', '91', '92'])).
% 14.69/14.88  thf('94', plain, (~ (v2_funct_1 @ sk_C)),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('95', plain,
% 14.69/14.88      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_C))
% 14.69/14.88        | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 14.69/14.88      inference('clc', [status(thm)], ['93', '94'])).
% 14.69/14.88  thf('96', plain,
% 14.69/14.88      ((~ (v2_funct_1 @ k1_xboole_0)
% 14.69/14.88        | ((sk_B) = (k1_relat_1 @ sk_D))
% 14.69/14.88        | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 14.69/14.88      inference('sup-', [status(thm)], ['50', '95'])).
% 14.69/14.88  thf('97', plain,
% 14.69/14.88      (![X2 : $i, X3 : $i]:
% 14.69/14.88         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 14.69/14.88      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 14.69/14.88  thf('98', plain,
% 14.69/14.88      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 14.69/14.88      inference('simplify', [status(thm)], ['97'])).
% 14.69/14.88  thf(dt_k6_partfun1, axiom,
% 14.69/14.88    (![A:$i]:
% 14.69/14.88     ( ( m1_subset_1 @
% 14.69/14.88         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 14.69/14.88       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 14.69/14.88  thf('99', plain,
% 14.69/14.88      (![X41 : $i]:
% 14.69/14.88         (m1_subset_1 @ (k6_partfun1 @ X41) @ 
% 14.69/14.88          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 14.69/14.88      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 14.69/14.88  thf(redefinition_k6_partfun1, axiom,
% 14.69/14.88    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 14.69/14.88  thf('100', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 14.69/14.88      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 14.69/14.88  thf('101', plain,
% 14.69/14.88      (![X41 : $i]:
% 14.69/14.88         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 14.69/14.88          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 14.69/14.88      inference('demod', [status(thm)], ['99', '100'])).
% 14.69/14.88  thf('102', plain,
% 14.69/14.88      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 14.69/14.88      inference('sup+', [status(thm)], ['98', '101'])).
% 14.69/14.88  thf('103', plain,
% 14.69/14.88      (![X4 : $i, X5 : $i]:
% 14.69/14.88         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 14.69/14.88      inference('cnf', [status(esa)], [t3_subset])).
% 14.69/14.88  thf('104', plain, ((r1_tarski @ (k6_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 14.69/14.88      inference('sup-', [status(thm)], ['102', '103'])).
% 14.69/14.88  thf('105', plain,
% 14.69/14.88      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 14.69/14.88      inference('cnf', [status(esa)], [t3_xboole_1])).
% 14.69/14.88  thf('106', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 14.69/14.88      inference('sup-', [status(thm)], ['104', '105'])).
% 14.69/14.88  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 14.69/14.88  thf('107', plain, (![X15 : $i]: (v2_funct_1 @ (k6_relat_1 @ X15))),
% 14.69/14.88      inference('cnf', [status(esa)], [t52_funct_1])).
% 14.69/14.88  thf('108', plain, ((v2_funct_1 @ k1_xboole_0)),
% 14.69/14.88      inference('sup+', [status(thm)], ['106', '107'])).
% 14.69/14.88  thf('109', plain,
% 14.69/14.88      ((((sk_B) = (k1_relat_1 @ sk_D)) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 14.69/14.88      inference('demod', [status(thm)], ['96', '108'])).
% 14.69/14.88  thf('110', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 14.69/14.88      inference('simplify', [status(thm)], ['109'])).
% 14.69/14.88  thf('111', plain,
% 14.69/14.88      (![X13 : $i, X14 : $i]:
% 14.69/14.88         (~ (v1_relat_1 @ X13)
% 14.69/14.88          | ~ (v1_funct_1 @ X13)
% 14.69/14.88          | (v2_funct_1 @ X13)
% 14.69/14.88          | ~ (r1_tarski @ (k2_relat_1 @ X13) @ (k1_relat_1 @ X14))
% 14.69/14.88          | ~ (v2_funct_1 @ (k5_relat_1 @ X13 @ X14))
% 14.69/14.88          | ~ (v1_funct_1 @ X14)
% 14.69/14.88          | ~ (v1_relat_1 @ X14))),
% 14.69/14.88      inference('cnf', [status(esa)], [t47_funct_1])).
% 14.69/14.88  thf('112', plain,
% 14.69/14.88      (![X0 : $i]:
% 14.69/14.88         (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_B)
% 14.69/14.88          | ~ (v1_relat_1 @ sk_D)
% 14.69/14.88          | ~ (v1_funct_1 @ sk_D)
% 14.69/14.88          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_D))
% 14.69/14.88          | (v2_funct_1 @ X0)
% 14.69/14.88          | ~ (v1_funct_1 @ X0)
% 14.69/14.88          | ~ (v1_relat_1 @ X0))),
% 14.69/14.88      inference('sup-', [status(thm)], ['110', '111'])).
% 14.69/14.88  thf('113', plain,
% 14.69/14.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('114', plain,
% 14.69/14.88      (![X7 : $i, X8 : $i]:
% 14.69/14.88         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 14.69/14.88          | (v1_relat_1 @ X7)
% 14.69/14.88          | ~ (v1_relat_1 @ X8))),
% 14.69/14.88      inference('cnf', [status(esa)], [cc2_relat_1])).
% 14.69/14.88  thf('115', plain,
% 14.69/14.88      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 14.69/14.88      inference('sup-', [status(thm)], ['113', '114'])).
% 14.69/14.88  thf('116', plain,
% 14.69/14.88      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 14.69/14.88      inference('cnf', [status(esa)], [fc6_relat_1])).
% 14.69/14.88  thf('117', plain, ((v1_relat_1 @ sk_D)),
% 14.69/14.88      inference('demod', [status(thm)], ['115', '116'])).
% 14.69/14.88  thf('118', plain, ((v1_funct_1 @ sk_D)),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('119', plain,
% 14.69/14.88      (![X0 : $i]:
% 14.69/14.88         (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_B)
% 14.69/14.88          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_D))
% 14.69/14.88          | (v2_funct_1 @ X0)
% 14.69/14.88          | ~ (v1_funct_1 @ X0)
% 14.69/14.88          | ~ (v1_relat_1 @ X0))),
% 14.69/14.88      inference('demod', [status(thm)], ['112', '117', '118'])).
% 14.69/14.88  thf('120', plain,
% 14.69/14.88      ((~ (v1_relat_1 @ sk_C)
% 14.69/14.88        | ~ (v1_funct_1 @ sk_C)
% 14.69/14.88        | (v2_funct_1 @ sk_C)
% 14.69/14.88        | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 14.69/14.88      inference('sup-', [status(thm)], ['10', '119'])).
% 14.69/14.88  thf('121', plain, ((v1_relat_1 @ sk_C)),
% 14.69/14.88      inference('demod', [status(thm)], ['7', '8'])).
% 14.69/14.88  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('123', plain,
% 14.69/14.88      (((v2_funct_1 @ sk_C) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 14.69/14.88      inference('demod', [status(thm)], ['120', '121', '122'])).
% 14.69/14.88  thf('124', plain, (~ (v2_funct_1 @ sk_C)),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('125', plain, (~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 14.69/14.88      inference('clc', [status(thm)], ['123', '124'])).
% 14.69/14.88  thf('126', plain,
% 14.69/14.88      ((r2_relset_1 @ sk_A @ sk_A @ 
% 14.69/14.88        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 14.69/14.88        (k6_partfun1 @ sk_A))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('127', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 14.69/14.88      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 14.69/14.88  thf('128', plain,
% 14.69/14.88      ((r2_relset_1 @ sk_A @ sk_A @ 
% 14.69/14.88        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 14.69/14.88        (k6_relat_1 @ sk_A))),
% 14.69/14.88      inference('demod', [status(thm)], ['126', '127'])).
% 14.69/14.88  thf('129', plain,
% 14.69/14.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('130', plain,
% 14.69/14.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.69/14.88         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 14.69/14.88            = (k5_relat_1 @ sk_C @ X0))
% 14.69/14.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 14.69/14.88          | ~ (v1_funct_1 @ X0))),
% 14.69/14.88      inference('demod', [status(thm)], ['14', '15'])).
% 14.69/14.88  thf('131', plain,
% 14.69/14.88      ((~ (v1_funct_1 @ sk_D)
% 14.69/14.88        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 14.69/14.88            = (k5_relat_1 @ sk_C @ sk_D)))),
% 14.69/14.88      inference('sup-', [status(thm)], ['129', '130'])).
% 14.69/14.88  thf('132', plain, ((v1_funct_1 @ sk_D)),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('133', plain,
% 14.69/14.88      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 14.69/14.88         = (k5_relat_1 @ sk_C @ sk_D))),
% 14.69/14.88      inference('demod', [status(thm)], ['131', '132'])).
% 14.69/14.88  thf('134', plain,
% 14.69/14.88      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 14.69/14.88        (k6_relat_1 @ sk_A))),
% 14.69/14.88      inference('demod', [status(thm)], ['128', '133'])).
% 14.69/14.88  thf('135', plain,
% 14.69/14.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('136', plain,
% 14.69/14.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.69/14.88         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 14.69/14.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 14.69/14.88          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 14.69/14.88          | ~ (v1_funct_1 @ X1))),
% 14.69/14.88      inference('demod', [status(thm)], ['39', '40'])).
% 14.69/14.88  thf('137', plain,
% 14.69/14.88      ((~ (v1_funct_1 @ sk_D)
% 14.69/14.88        | (m1_subset_1 @ 
% 14.69/14.88           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 14.69/14.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 14.69/14.88      inference('sup-', [status(thm)], ['135', '136'])).
% 14.69/14.88  thf('138', plain, ((v1_funct_1 @ sk_D)),
% 14.69/14.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.69/14.88  thf('139', plain,
% 14.69/14.88      ((m1_subset_1 @ 
% 14.69/14.88        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 14.69/14.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 14.69/14.88      inference('demod', [status(thm)], ['137', '138'])).
% 14.69/14.88  thf('140', plain,
% 14.69/14.88      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 14.69/14.88         = (k5_relat_1 @ sk_C @ sk_D))),
% 14.69/14.88      inference('demod', [status(thm)], ['131', '132'])).
% 14.69/14.88  thf('141', plain,
% 14.69/14.88      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 14.69/14.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 14.69/14.88      inference('demod', [status(thm)], ['139', '140'])).
% 14.69/14.88  thf(redefinition_r2_relset_1, axiom,
% 14.69/14.88    (![A:$i,B:$i,C:$i,D:$i]:
% 14.69/14.88     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 14.69/14.88         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 14.69/14.88       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 14.69/14.88  thf('142', plain,
% 14.69/14.88      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 14.69/14.88         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 14.69/14.88          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 14.69/14.88          | ((X22) = (X25))
% 14.69/14.88          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 14.69/14.88      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 14.69/14.88  thf('143', plain,
% 14.69/14.88      (![X0 : $i]:
% 14.69/14.88         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 14.69/14.88          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 14.69/14.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 14.69/14.88      inference('sup-', [status(thm)], ['141', '142'])).
% 14.69/14.88  thf('144', plain,
% 14.69/14.88      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 14.69/14.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 14.69/14.88        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 14.69/14.88      inference('sup-', [status(thm)], ['134', '143'])).
% 14.69/14.88  thf('145', plain,
% 14.69/14.88      (![X41 : $i]:
% 14.69/14.88         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 14.69/14.88          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 14.69/14.88      inference('demod', [status(thm)], ['99', '100'])).
% 14.69/14.88  thf('146', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 14.69/14.88      inference('demod', [status(thm)], ['144', '145'])).
% 14.69/14.88  thf('147', plain, (![X15 : $i]: (v2_funct_1 @ (k6_relat_1 @ X15))),
% 14.69/14.88      inference('cnf', [status(esa)], [t52_funct_1])).
% 14.69/14.88  thf('148', plain, ($false),
% 14.69/14.88      inference('demod', [status(thm)], ['125', '146', '147'])).
% 14.69/14.88  
% 14.69/14.88  % SZS output end Refutation
% 14.69/14.88  
% 14.69/14.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
