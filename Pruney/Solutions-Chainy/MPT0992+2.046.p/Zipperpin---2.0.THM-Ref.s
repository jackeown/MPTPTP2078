%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dJABuFOGd0

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:41 EST 2020

% Result     : Theorem 3.06s
% Output     : Refutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  200 (1755 expanded)
%              Number of leaves         :   39 ( 498 expanded)
%              Depth                    :   30
%              Number of atoms          : 1553 (31398 expanded)
%              Number of equality atoms :  127 (2080 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t38_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
            & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
            & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ C @ A )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ( ( k2_partfun1 @ X34 @ X35 @ X33 @ X36 )
        = ( k7_relat_1 @ X33 @ X36 ) ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X30 @ X31 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('15',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5','12','13','14'])).

thf('16',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('27',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('34',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v5_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['36','39'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X38 )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X37 ) @ X38 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','47'])).

thf('49',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('55',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('58',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( v4_relat_1 @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D )
        | ( sk_D
          = ( k7_relat_1 @ sk_D @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5','12','13','14'])).

thf('67',plain,
    ( ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('69',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('71',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('72',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('74',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','55'])).

thf('75',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('77',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','55'])).

thf('79',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('80',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('84',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','55'])).

thf('85',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('86',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( v5_relat_1 @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v5_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D )
        | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('95',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','95'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('97',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
          = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('101',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','101'])).

thf('103',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23
       != ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ~ ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
        | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 )
        | ~ ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','55'])).

thf('107',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('108',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X22 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('111',plain,(
    ! [X21: $i] :
      ( zip_tseitin_0 @ X21 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['109','111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','112'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','113'])).

thf('115',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['67','72','73','74','75','76','77','114'])).

thf('116',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('117',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['115','116'])).

thf('118',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['50','117'])).

thf('119',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['48','118'])).

thf('120',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','119'])).

thf('121',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['50','117'])).

thf('122',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['120','121'])).

thf('123',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['23','122'])).

thf('124',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X30 @ X31 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('135',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v5_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('141',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['139','142'])).

thf('144',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X38 )
      | ( v1_funct_2 @ X37 @ ( k1_relat_1 @ X37 ) @ X38 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('147',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('148',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['128','148'])).

thf('150',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','149'])).

thf('151',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','127'])).

thf('152',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['139','142'])).

thf('153',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X38 )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X37 ) @ X38 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('156',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('157',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['151','157'])).

thf('159',plain,(
    $false ),
    inference(demod,[status(thm)],['150','158'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dJABuFOGd0
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:14:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.06/3.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.06/3.24  % Solved by: fo/fo7.sh
% 3.06/3.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.06/3.24  % done 1238 iterations in 2.794s
% 3.06/3.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.06/3.24  % SZS output start Refutation
% 3.06/3.24  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.06/3.24  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.06/3.24  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.06/3.24  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.06/3.24  thf(sk_D_type, type, sk_D: $i).
% 3.06/3.24  thf(sk_A_type, type, sk_A: $i).
% 3.06/3.24  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 3.06/3.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.06/3.24  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.06/3.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.06/3.24  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.06/3.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.06/3.24  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.06/3.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.06/3.24  thf(sk_B_type, type, sk_B: $i).
% 3.06/3.24  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.06/3.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.06/3.24  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.06/3.24  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.06/3.24  thf(sk_C_type, type, sk_C: $i).
% 3.06/3.24  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.06/3.24  thf(t38_funct_2, conjecture,
% 3.06/3.24    (![A:$i,B:$i,C:$i,D:$i]:
% 3.06/3.24     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.06/3.24         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.06/3.24       ( ( r1_tarski @ C @ A ) =>
% 3.06/3.24         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 3.06/3.24           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 3.06/3.24             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 3.06/3.24             ( m1_subset_1 @
% 3.06/3.24               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 3.06/3.24               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 3.06/3.24  thf(zf_stmt_0, negated_conjecture,
% 3.06/3.24    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.06/3.24        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.06/3.24            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.06/3.24          ( ( r1_tarski @ C @ A ) =>
% 3.06/3.24            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 3.06/3.24              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 3.06/3.24                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 3.06/3.24                ( m1_subset_1 @
% 3.06/3.24                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 3.06/3.24                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 3.06/3.24    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 3.06/3.24  thf('0', plain,
% 3.06/3.24      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 3.06/3.24        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 3.06/3.24             sk_B)
% 3.06/3.24        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 3.06/3.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf('1', plain,
% 3.06/3.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf(redefinition_k2_partfun1, axiom,
% 3.06/3.24    (![A:$i,B:$i,C:$i,D:$i]:
% 3.06/3.24     ( ( ( v1_funct_1 @ C ) & 
% 3.06/3.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.06/3.24       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 3.06/3.24  thf('2', plain,
% 3.06/3.24      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.06/3.24         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.06/3.24          | ~ (v1_funct_1 @ X33)
% 3.06/3.24          | ((k2_partfun1 @ X34 @ X35 @ X33 @ X36) = (k7_relat_1 @ X33 @ X36)))),
% 3.06/3.24      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 3.06/3.24  thf('3', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 3.06/3.24          | ~ (v1_funct_1 @ sk_D))),
% 3.06/3.24      inference('sup-', [status(thm)], ['1', '2'])).
% 3.06/3.24  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf('5', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 3.06/3.24      inference('demod', [status(thm)], ['3', '4'])).
% 3.06/3.24  thf('6', plain,
% 3.06/3.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf(dt_k2_partfun1, axiom,
% 3.06/3.24    (![A:$i,B:$i,C:$i,D:$i]:
% 3.06/3.24     ( ( ( v1_funct_1 @ C ) & 
% 3.06/3.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.06/3.24       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 3.06/3.24         ( m1_subset_1 @
% 3.06/3.24           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 3.06/3.24           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 3.06/3.24  thf('7', plain,
% 3.06/3.24      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 3.06/3.24         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 3.06/3.24          | ~ (v1_funct_1 @ X29)
% 3.06/3.24          | (v1_funct_1 @ (k2_partfun1 @ X30 @ X31 @ X29 @ X32)))),
% 3.06/3.24      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 3.06/3.24  thf('8', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 3.06/3.24          | ~ (v1_funct_1 @ sk_D))),
% 3.06/3.24      inference('sup-', [status(thm)], ['6', '7'])).
% 3.06/3.24  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf('10', plain,
% 3.06/3.24      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 3.06/3.24      inference('demod', [status(thm)], ['8', '9'])).
% 3.06/3.24  thf('11', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 3.06/3.24      inference('demod', [status(thm)], ['3', '4'])).
% 3.06/3.24  thf('12', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.06/3.24      inference('demod', [status(thm)], ['10', '11'])).
% 3.06/3.24  thf('13', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 3.06/3.24      inference('demod', [status(thm)], ['3', '4'])).
% 3.06/3.24  thf('14', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 3.06/3.24      inference('demod', [status(thm)], ['3', '4'])).
% 3.06/3.24  thf('15', plain,
% 3.06/3.24      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 3.06/3.24        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 3.06/3.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 3.06/3.24      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 3.06/3.24  thf('16', plain, ((r1_tarski @ sk_C @ sk_A)),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf('17', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf(d1_funct_2, axiom,
% 3.06/3.24    (![A:$i,B:$i,C:$i]:
% 3.06/3.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.06/3.24       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.06/3.24           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.06/3.24             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.06/3.24         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.06/3.24           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.06/3.24             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.06/3.24  thf(zf_stmt_1, axiom,
% 3.06/3.24    (![C:$i,B:$i,A:$i]:
% 3.06/3.24     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.06/3.24       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.06/3.24  thf('18', plain,
% 3.06/3.24      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.06/3.24         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 3.06/3.24          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 3.06/3.24          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.06/3.24  thf('19', plain,
% 3.06/3.24      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 3.06/3.24        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 3.06/3.24      inference('sup-', [status(thm)], ['17', '18'])).
% 3.06/3.24  thf('20', plain,
% 3.06/3.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf(redefinition_k1_relset_1, axiom,
% 3.06/3.24    (![A:$i,B:$i,C:$i]:
% 3.06/3.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.06/3.24       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.06/3.24  thf('21', plain,
% 3.06/3.24      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.06/3.24         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 3.06/3.24          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 3.06/3.24      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.06/3.24  thf('22', plain,
% 3.06/3.24      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.06/3.24      inference('sup-', [status(thm)], ['20', '21'])).
% 3.06/3.24  thf('23', plain,
% 3.06/3.24      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.06/3.24      inference('demod', [status(thm)], ['19', '22'])).
% 3.06/3.24  thf(zf_stmt_2, axiom,
% 3.06/3.24    (![B:$i,A:$i]:
% 3.06/3.24     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.06/3.24       ( zip_tseitin_0 @ B @ A ) ))).
% 3.06/3.24  thf('24', plain,
% 3.06/3.24      (![X21 : $i, X22 : $i]:
% 3.06/3.24         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.06/3.24  thf('25', plain,
% 3.06/3.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.06/3.24  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.06/3.24  thf(zf_stmt_5, axiom,
% 3.06/3.24    (![A:$i,B:$i,C:$i]:
% 3.06/3.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.06/3.24       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.06/3.24         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.06/3.24           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.06/3.24             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.06/3.24  thf('26', plain,
% 3.06/3.24      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.06/3.24         (~ (zip_tseitin_0 @ X26 @ X27)
% 3.06/3.24          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 3.06/3.24          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.06/3.24  thf('27', plain,
% 3.06/3.24      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.06/3.24      inference('sup-', [status(thm)], ['25', '26'])).
% 3.06/3.24  thf('28', plain,
% 3.06/3.24      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 3.06/3.24      inference('sup-', [status(thm)], ['24', '27'])).
% 3.06/3.24  thf('29', plain,
% 3.06/3.24      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.06/3.24      inference('demod', [status(thm)], ['19', '22'])).
% 3.06/3.24  thf('30', plain,
% 3.06/3.24      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.06/3.24      inference('sup-', [status(thm)], ['28', '29'])).
% 3.06/3.24  thf('31', plain,
% 3.06/3.24      (![X21 : $i, X22 : $i]:
% 3.06/3.24         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.06/3.24  thf('32', plain,
% 3.06/3.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf(cc2_relset_1, axiom,
% 3.06/3.24    (![A:$i,B:$i,C:$i]:
% 3.06/3.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.06/3.24       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.06/3.24  thf('33', plain,
% 3.06/3.24      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.06/3.24         ((v5_relat_1 @ X15 @ X17)
% 3.06/3.24          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.06/3.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.06/3.24  thf('34', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 3.06/3.24      inference('sup-', [status(thm)], ['32', '33'])).
% 3.06/3.24  thf(d19_relat_1, axiom,
% 3.06/3.24    (![A:$i,B:$i]:
% 3.06/3.24     ( ( v1_relat_1 @ B ) =>
% 3.06/3.24       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.06/3.24  thf('35', plain,
% 3.06/3.24      (![X4 : $i, X5 : $i]:
% 3.06/3.24         (~ (v5_relat_1 @ X4 @ X5)
% 3.06/3.24          | (r1_tarski @ (k2_relat_1 @ X4) @ X5)
% 3.06/3.24          | ~ (v1_relat_1 @ X4))),
% 3.06/3.24      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.06/3.24  thf('36', plain,
% 3.06/3.24      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 3.06/3.24      inference('sup-', [status(thm)], ['34', '35'])).
% 3.06/3.24  thf('37', plain,
% 3.06/3.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf(cc1_relset_1, axiom,
% 3.06/3.24    (![A:$i,B:$i,C:$i]:
% 3.06/3.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.06/3.24       ( v1_relat_1 @ C ) ))).
% 3.06/3.24  thf('38', plain,
% 3.06/3.24      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.06/3.24         ((v1_relat_1 @ X12)
% 3.06/3.24          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 3.06/3.24      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.06/3.24  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 3.06/3.24      inference('sup-', [status(thm)], ['37', '38'])).
% 3.06/3.24  thf('40', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 3.06/3.24      inference('demod', [status(thm)], ['36', '39'])).
% 3.06/3.24  thf(t4_funct_2, axiom,
% 3.06/3.24    (![A:$i,B:$i]:
% 3.06/3.24     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.06/3.24       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 3.06/3.24         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 3.06/3.24           ( m1_subset_1 @
% 3.06/3.24             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 3.06/3.24  thf('41', plain,
% 3.06/3.24      (![X37 : $i, X38 : $i]:
% 3.06/3.24         (~ (r1_tarski @ (k2_relat_1 @ X37) @ X38)
% 3.06/3.24          | (m1_subset_1 @ X37 @ 
% 3.06/3.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X37) @ X38)))
% 3.06/3.24          | ~ (v1_funct_1 @ X37)
% 3.06/3.24          | ~ (v1_relat_1 @ X37))),
% 3.06/3.24      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.06/3.24  thf('42', plain,
% 3.06/3.24      ((~ (v1_relat_1 @ sk_D)
% 3.06/3.24        | ~ (v1_funct_1 @ sk_D)
% 3.06/3.24        | (m1_subset_1 @ sk_D @ 
% 3.06/3.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B))))),
% 3.06/3.24      inference('sup-', [status(thm)], ['40', '41'])).
% 3.06/3.24  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 3.06/3.24      inference('sup-', [status(thm)], ['37', '38'])).
% 3.06/3.24  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf('45', plain,
% 3.06/3.24      ((m1_subset_1 @ sk_D @ 
% 3.06/3.24        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 3.06/3.24      inference('demod', [status(thm)], ['42', '43', '44'])).
% 3.06/3.24  thf('46', plain,
% 3.06/3.24      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.06/3.24         (~ (zip_tseitin_0 @ X26 @ X27)
% 3.06/3.24          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 3.06/3.24          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.06/3.24  thf('47', plain,
% 3.06/3.24      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D))
% 3.06/3.24        | ~ (zip_tseitin_0 @ sk_B @ (k1_relat_1 @ sk_D)))),
% 3.06/3.24      inference('sup-', [status(thm)], ['45', '46'])).
% 3.06/3.24  thf('48', plain,
% 3.06/3.24      ((((sk_B) = (k1_xboole_0))
% 3.06/3.24        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D)))),
% 3.06/3.24      inference('sup-', [status(thm)], ['31', '47'])).
% 3.06/3.24  thf('49', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf('50', plain,
% 3.06/3.24      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.06/3.24      inference('split', [status(esa)], ['49'])).
% 3.06/3.24  thf('51', plain,
% 3.06/3.24      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('split', [status(esa)], ['49'])).
% 3.06/3.24  thf('52', plain,
% 3.06/3.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf('53', plain,
% 3.06/3.24      (((m1_subset_1 @ sk_D @ 
% 3.06/3.24         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('sup+', [status(thm)], ['51', '52'])).
% 3.06/3.24  thf(t113_zfmisc_1, axiom,
% 3.06/3.24    (![A:$i,B:$i]:
% 3.06/3.24     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.06/3.24       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.06/3.24  thf('54', plain,
% 3.06/3.24      (![X2 : $i, X3 : $i]:
% 3.06/3.24         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 3.06/3.24      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.06/3.24  thf('55', plain,
% 3.06/3.24      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 3.06/3.24      inference('simplify', [status(thm)], ['54'])).
% 3.06/3.24  thf('56', plain,
% 3.06/3.24      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('demod', [status(thm)], ['53', '55'])).
% 3.06/3.24  thf('57', plain,
% 3.06/3.24      (![X2 : $i, X3 : $i]:
% 3.06/3.24         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 3.06/3.24      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.06/3.24  thf('58', plain,
% 3.06/3.24      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 3.06/3.24      inference('simplify', [status(thm)], ['57'])).
% 3.06/3.24  thf('59', plain,
% 3.06/3.24      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.06/3.24         ((v4_relat_1 @ X15 @ X16)
% 3.06/3.24          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.06/3.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.06/3.24  thf('60', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i]:
% 3.06/3.24         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.06/3.24          | (v4_relat_1 @ X1 @ X0))),
% 3.06/3.24      inference('sup-', [status(thm)], ['58', '59'])).
% 3.06/3.24  thf('61', plain,
% 3.06/3.24      ((![X0 : $i]: (v4_relat_1 @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('sup-', [status(thm)], ['56', '60'])).
% 3.06/3.24  thf(t209_relat_1, axiom,
% 3.06/3.24    (![A:$i,B:$i]:
% 3.06/3.24     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 3.06/3.24       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 3.06/3.24  thf('62', plain,
% 3.06/3.24      (![X8 : $i, X9 : $i]:
% 3.06/3.24         (((X8) = (k7_relat_1 @ X8 @ X9))
% 3.06/3.24          | ~ (v4_relat_1 @ X8 @ X9)
% 3.06/3.24          | ~ (v1_relat_1 @ X8))),
% 3.06/3.24      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.06/3.24  thf('63', plain,
% 3.06/3.24      ((![X0 : $i]:
% 3.06/3.24          (~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ X0))))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('sup-', [status(thm)], ['61', '62'])).
% 3.06/3.24  thf('64', plain, ((v1_relat_1 @ sk_D)),
% 3.06/3.24      inference('sup-', [status(thm)], ['37', '38'])).
% 3.06/3.24  thf('65', plain,
% 3.06/3.24      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('demod', [status(thm)], ['63', '64'])).
% 3.06/3.24  thf('66', plain,
% 3.06/3.24      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 3.06/3.24        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 3.06/3.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 3.06/3.24      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 3.06/3.24  thf('67', plain,
% 3.06/3.24      (((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 3.06/3.24         | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('sup-', [status(thm)], ['65', '66'])).
% 3.06/3.24  thf('68', plain,
% 3.06/3.24      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('split', [status(esa)], ['49'])).
% 3.06/3.24  thf('69', plain, ((r1_tarski @ sk_C @ sk_A)),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf('70', plain,
% 3.06/3.24      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('sup+', [status(thm)], ['68', '69'])).
% 3.06/3.24  thf(t3_xboole_1, axiom,
% 3.06/3.24    (![A:$i]:
% 3.06/3.24     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.06/3.24  thf('71', plain,
% 3.06/3.24      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 3.06/3.24      inference('cnf', [status(esa)], [t3_xboole_1])).
% 3.06/3.24  thf('72', plain,
% 3.06/3.24      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('sup-', [status(thm)], ['70', '71'])).
% 3.06/3.24  thf('73', plain,
% 3.06/3.24      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 3.06/3.24      inference('simplify', [status(thm)], ['54'])).
% 3.06/3.24  thf('74', plain,
% 3.06/3.24      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('demod', [status(thm)], ['53', '55'])).
% 3.06/3.24  thf('75', plain,
% 3.06/3.24      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('sup-', [status(thm)], ['70', '71'])).
% 3.06/3.24  thf('76', plain,
% 3.06/3.24      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('demod', [status(thm)], ['63', '64'])).
% 3.06/3.24  thf('77', plain,
% 3.06/3.24      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('sup-', [status(thm)], ['70', '71'])).
% 3.06/3.24  thf('78', plain,
% 3.06/3.24      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('demod', [status(thm)], ['53', '55'])).
% 3.06/3.24  thf('79', plain,
% 3.06/3.24      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 3.06/3.24      inference('simplify', [status(thm)], ['54'])).
% 3.06/3.24  thf('80', plain,
% 3.06/3.24      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.06/3.24         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 3.06/3.24          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 3.06/3.24      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.06/3.24  thf('81', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i]:
% 3.06/3.24         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.06/3.24          | ((k1_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k1_relat_1 @ X1)))),
% 3.06/3.24      inference('sup-', [status(thm)], ['79', '80'])).
% 3.06/3.24  thf('82', plain,
% 3.06/3.24      ((![X0 : $i]:
% 3.06/3.24          ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_relat_1 @ sk_D)))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('sup-', [status(thm)], ['78', '81'])).
% 3.06/3.24  thf('83', plain,
% 3.06/3.24      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('demod', [status(thm)], ['63', '64'])).
% 3.06/3.24  thf('84', plain,
% 3.06/3.24      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('demod', [status(thm)], ['53', '55'])).
% 3.06/3.24  thf('85', plain,
% 3.06/3.24      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 3.06/3.24      inference('simplify', [status(thm)], ['54'])).
% 3.06/3.24  thf('86', plain,
% 3.06/3.24      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.06/3.24         ((v5_relat_1 @ X15 @ X17)
% 3.06/3.24          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.06/3.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.06/3.24  thf('87', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i]:
% 3.06/3.24         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.06/3.24          | (v5_relat_1 @ X1 @ X0))),
% 3.06/3.24      inference('sup-', [status(thm)], ['85', '86'])).
% 3.06/3.24  thf('88', plain,
% 3.06/3.24      ((![X0 : $i]: (v5_relat_1 @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('sup-', [status(thm)], ['84', '87'])).
% 3.06/3.24  thf('89', plain,
% 3.06/3.24      (![X4 : $i, X5 : $i]:
% 3.06/3.24         (~ (v5_relat_1 @ X4 @ X5)
% 3.06/3.24          | (r1_tarski @ (k2_relat_1 @ X4) @ X5)
% 3.06/3.24          | ~ (v1_relat_1 @ X4))),
% 3.06/3.24      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.06/3.24  thf('90', plain,
% 3.06/3.24      ((![X0 : $i]:
% 3.06/3.24          (~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ X0)))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('sup-', [status(thm)], ['88', '89'])).
% 3.06/3.24  thf('91', plain, ((v1_relat_1 @ sk_D)),
% 3.06/3.24      inference('sup-', [status(thm)], ['37', '38'])).
% 3.06/3.24  thf('92', plain,
% 3.06/3.24      ((![X0 : $i]: (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('demod', [status(thm)], ['90', '91'])).
% 3.06/3.24  thf('93', plain,
% 3.06/3.24      ((![X0 : $i]: (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('demod', [status(thm)], ['90', '91'])).
% 3.06/3.24  thf('94', plain,
% 3.06/3.24      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 3.06/3.24      inference('cnf', [status(esa)], [t3_xboole_1])).
% 3.06/3.24  thf('95', plain,
% 3.06/3.24      ((((k2_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('sup-', [status(thm)], ['93', '94'])).
% 3.06/3.24  thf('96', plain,
% 3.06/3.24      ((![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('demod', [status(thm)], ['92', '95'])).
% 3.06/3.24  thf(t91_relat_1, axiom,
% 3.06/3.24    (![A:$i,B:$i]:
% 3.06/3.24     ( ( v1_relat_1 @ B ) =>
% 3.06/3.24       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 3.06/3.24         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 3.06/3.24  thf('97', plain,
% 3.06/3.24      (![X10 : $i, X11 : $i]:
% 3.06/3.24         (~ (r1_tarski @ X10 @ (k1_relat_1 @ X11))
% 3.06/3.24          | ((k1_relat_1 @ (k7_relat_1 @ X11 @ X10)) = (X10))
% 3.06/3.24          | ~ (v1_relat_1 @ X11))),
% 3.06/3.24      inference('cnf', [status(esa)], [t91_relat_1])).
% 3.06/3.24  thf('98', plain,
% 3.06/3.24      ((![X0 : $i]:
% 3.06/3.24          (~ (v1_relat_1 @ X0)
% 3.06/3.24           | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('sup-', [status(thm)], ['96', '97'])).
% 3.06/3.24  thf('99', plain,
% 3.06/3.24      (((((k1_relat_1 @ sk_D) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_D)))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('sup+', [status(thm)], ['83', '98'])).
% 3.06/3.24  thf('100', plain, ((v1_relat_1 @ sk_D)),
% 3.06/3.24      inference('sup-', [status(thm)], ['37', '38'])).
% 3.06/3.24  thf('101', plain,
% 3.06/3.24      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('demod', [status(thm)], ['99', '100'])).
% 3.06/3.24  thf('102', plain,
% 3.06/3.24      ((![X0 : $i]: ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_xboole_0)))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('demod', [status(thm)], ['82', '101'])).
% 3.06/3.24  thf('103', plain,
% 3.06/3.24      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.06/3.24         (((X23) != (k1_relset_1 @ X23 @ X24 @ X25))
% 3.06/3.24          | (v1_funct_2 @ X25 @ X23 @ X24)
% 3.06/3.24          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.06/3.24  thf('104', plain,
% 3.06/3.24      ((![X0 : $i]:
% 3.06/3.24          (((k1_xboole_0) != (k1_xboole_0))
% 3.06/3.24           | ~ (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0)
% 3.06/3.24           | (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0)))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('sup-', [status(thm)], ['102', '103'])).
% 3.06/3.24  thf('105', plain,
% 3.06/3.24      ((![X0 : $i]:
% 3.06/3.24          ((v1_funct_2 @ sk_D @ k1_xboole_0 @ X0)
% 3.06/3.24           | ~ (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0)))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('simplify', [status(thm)], ['104'])).
% 3.06/3.24  thf('106', plain,
% 3.06/3.24      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('demod', [status(thm)], ['53', '55'])).
% 3.06/3.24  thf('107', plain,
% 3.06/3.24      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 3.06/3.24      inference('simplify', [status(thm)], ['54'])).
% 3.06/3.24  thf('108', plain,
% 3.06/3.24      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.06/3.24         (~ (zip_tseitin_0 @ X26 @ X27)
% 3.06/3.24          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 3.06/3.24          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.06/3.24  thf('109', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i]:
% 3.06/3.24         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.06/3.24          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 3.06/3.24          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 3.06/3.24      inference('sup-', [status(thm)], ['107', '108'])).
% 3.06/3.24  thf('110', plain,
% 3.06/3.24      (![X21 : $i, X22 : $i]:
% 3.06/3.24         ((zip_tseitin_0 @ X21 @ X22) | ((X22) != (k1_xboole_0)))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.06/3.24  thf('111', plain, (![X21 : $i]: (zip_tseitin_0 @ X21 @ k1_xboole_0)),
% 3.06/3.24      inference('simplify', [status(thm)], ['110'])).
% 3.06/3.24  thf('112', plain,
% 3.06/3.24      (![X0 : $i, X1 : $i]:
% 3.06/3.24         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.06/3.24          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 3.06/3.24      inference('demod', [status(thm)], ['109', '111'])).
% 3.06/3.24  thf('113', plain,
% 3.06/3.24      ((![X0 : $i]: (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('sup-', [status(thm)], ['106', '112'])).
% 3.06/3.24  thf('114', plain,
% 3.06/3.24      ((![X0 : $i]: (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0))
% 3.06/3.24         <= ((((sk_A) = (k1_xboole_0))))),
% 3.06/3.24      inference('demod', [status(thm)], ['105', '113'])).
% 3.06/3.24  thf('115', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 3.06/3.24      inference('demod', [status(thm)],
% 3.06/3.24                ['67', '72', '73', '74', '75', '76', '77', '114'])).
% 3.06/3.24  thf('116', plain,
% 3.06/3.24      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 3.06/3.24      inference('split', [status(esa)], ['49'])).
% 3.06/3.24  thf('117', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 3.06/3.24      inference('sat_resolution*', [status(thm)], ['115', '116'])).
% 3.06/3.24  thf('118', plain, (((sk_B) != (k1_xboole_0))),
% 3.06/3.24      inference('simpl_trail', [status(thm)], ['50', '117'])).
% 3.06/3.24  thf('119', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D))),
% 3.06/3.24      inference('simplify_reflect-', [status(thm)], ['48', '118'])).
% 3.06/3.24  thf('120', plain,
% 3.06/3.24      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 3.06/3.24      inference('sup+', [status(thm)], ['30', '119'])).
% 3.06/3.24  thf('121', plain, (((sk_B) != (k1_xboole_0))),
% 3.06/3.24      inference('simpl_trail', [status(thm)], ['50', '117'])).
% 3.06/3.24  thf('122', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 3.06/3.24      inference('simplify_reflect-', [status(thm)], ['120', '121'])).
% 3.06/3.24  thf('123', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.06/3.24      inference('demod', [status(thm)], ['23', '122'])).
% 3.06/3.24  thf('124', plain,
% 3.06/3.24      (![X10 : $i, X11 : $i]:
% 3.06/3.24         (~ (r1_tarski @ X10 @ (k1_relat_1 @ X11))
% 3.06/3.24          | ((k1_relat_1 @ (k7_relat_1 @ X11 @ X10)) = (X10))
% 3.06/3.24          | ~ (v1_relat_1 @ X11))),
% 3.06/3.24      inference('cnf', [status(esa)], [t91_relat_1])).
% 3.06/3.24  thf('125', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         (~ (r1_tarski @ X0 @ sk_A)
% 3.06/3.24          | ~ (v1_relat_1 @ sk_D)
% 3.06/3.24          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 3.06/3.24      inference('sup-', [status(thm)], ['123', '124'])).
% 3.06/3.24  thf('126', plain, ((v1_relat_1 @ sk_D)),
% 3.06/3.24      inference('sup-', [status(thm)], ['37', '38'])).
% 3.06/3.24  thf('127', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         (~ (r1_tarski @ X0 @ sk_A)
% 3.06/3.24          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 3.06/3.24      inference('demod', [status(thm)], ['125', '126'])).
% 3.06/3.24  thf('128', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 3.06/3.24      inference('sup-', [status(thm)], ['16', '127'])).
% 3.06/3.24  thf('129', plain,
% 3.06/3.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf('130', plain,
% 3.06/3.24      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 3.06/3.24         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 3.06/3.24          | ~ (v1_funct_1 @ X29)
% 3.06/3.24          | (m1_subset_1 @ (k2_partfun1 @ X30 @ X31 @ X29 @ X32) @ 
% 3.06/3.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 3.06/3.24      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 3.06/3.24  thf('131', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 3.06/3.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.06/3.24          | ~ (v1_funct_1 @ sk_D))),
% 3.06/3.24      inference('sup-', [status(thm)], ['129', '130'])).
% 3.06/3.24  thf('132', plain, ((v1_funct_1 @ sk_D)),
% 3.06/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.24  thf('133', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 3.06/3.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.06/3.24      inference('demod', [status(thm)], ['131', '132'])).
% 3.06/3.24  thf('134', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 3.06/3.24      inference('demod', [status(thm)], ['3', '4'])).
% 3.06/3.24  thf('135', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.06/3.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.06/3.24      inference('demod', [status(thm)], ['133', '134'])).
% 3.06/3.24  thf('136', plain,
% 3.06/3.24      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.06/3.24         ((v5_relat_1 @ X15 @ X17)
% 3.06/3.24          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.06/3.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.06/3.24  thf('137', plain,
% 3.06/3.24      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 3.06/3.24      inference('sup-', [status(thm)], ['135', '136'])).
% 3.06/3.24  thf('138', plain,
% 3.06/3.24      (![X4 : $i, X5 : $i]:
% 3.06/3.24         (~ (v5_relat_1 @ X4 @ X5)
% 3.06/3.24          | (r1_tarski @ (k2_relat_1 @ X4) @ X5)
% 3.06/3.24          | ~ (v1_relat_1 @ X4))),
% 3.06/3.24      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.06/3.24  thf('139', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 3.06/3.24          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 3.06/3.24      inference('sup-', [status(thm)], ['137', '138'])).
% 3.06/3.24  thf('140', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.06/3.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.06/3.24      inference('demod', [status(thm)], ['133', '134'])).
% 3.06/3.24  thf('141', plain,
% 3.06/3.24      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.06/3.24         ((v1_relat_1 @ X12)
% 3.06/3.24          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 3.06/3.24      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.06/3.24  thf('142', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.06/3.24      inference('sup-', [status(thm)], ['140', '141'])).
% 3.06/3.24  thf('143', plain,
% 3.06/3.24      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 3.06/3.24      inference('demod', [status(thm)], ['139', '142'])).
% 3.06/3.24  thf('144', plain,
% 3.06/3.24      (![X37 : $i, X38 : $i]:
% 3.06/3.24         (~ (r1_tarski @ (k2_relat_1 @ X37) @ X38)
% 3.06/3.24          | (v1_funct_2 @ X37 @ (k1_relat_1 @ X37) @ X38)
% 3.06/3.24          | ~ (v1_funct_1 @ X37)
% 3.06/3.24          | ~ (v1_relat_1 @ X37))),
% 3.06/3.24      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.06/3.24  thf('145', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 3.06/3.24          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 3.06/3.24          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.06/3.24             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 3.06/3.24      inference('sup-', [status(thm)], ['143', '144'])).
% 3.06/3.24  thf('146', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.06/3.24      inference('sup-', [status(thm)], ['140', '141'])).
% 3.06/3.24  thf('147', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.06/3.24      inference('demod', [status(thm)], ['10', '11'])).
% 3.06/3.24  thf('148', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.06/3.24          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 3.06/3.24      inference('demod', [status(thm)], ['145', '146', '147'])).
% 3.06/3.24  thf('149', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 3.06/3.24      inference('sup+', [status(thm)], ['128', '148'])).
% 3.06/3.24  thf('150', plain,
% 3.06/3.24      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 3.06/3.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 3.06/3.24      inference('demod', [status(thm)], ['15', '149'])).
% 3.06/3.24  thf('151', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 3.06/3.24      inference('sup-', [status(thm)], ['16', '127'])).
% 3.06/3.24  thf('152', plain,
% 3.06/3.24      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 3.06/3.24      inference('demod', [status(thm)], ['139', '142'])).
% 3.06/3.24  thf('153', plain,
% 3.06/3.24      (![X37 : $i, X38 : $i]:
% 3.06/3.24         (~ (r1_tarski @ (k2_relat_1 @ X37) @ X38)
% 3.06/3.24          | (m1_subset_1 @ X37 @ 
% 3.06/3.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X37) @ X38)))
% 3.06/3.24          | ~ (v1_funct_1 @ X37)
% 3.06/3.24          | ~ (v1_relat_1 @ X37))),
% 3.06/3.24      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.06/3.24  thf('154', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 3.06/3.24          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 3.06/3.24          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.06/3.24             (k1_zfmisc_1 @ 
% 3.06/3.24              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 3.06/3.24      inference('sup-', [status(thm)], ['152', '153'])).
% 3.06/3.24  thf('155', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.06/3.24      inference('sup-', [status(thm)], ['140', '141'])).
% 3.06/3.24  thf('156', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.06/3.24      inference('demod', [status(thm)], ['10', '11'])).
% 3.06/3.24  thf('157', plain,
% 3.06/3.24      (![X0 : $i]:
% 3.06/3.24         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.06/3.24          (k1_zfmisc_1 @ 
% 3.06/3.24           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 3.06/3.24      inference('demod', [status(thm)], ['154', '155', '156'])).
% 3.06/3.24  thf('158', plain,
% 3.06/3.24      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 3.06/3.24        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 3.06/3.24      inference('sup+', [status(thm)], ['151', '157'])).
% 3.06/3.24  thf('159', plain, ($false), inference('demod', [status(thm)], ['150', '158'])).
% 3.06/3.24  
% 3.06/3.24  % SZS output end Refutation
% 3.06/3.24  
% 3.06/3.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
