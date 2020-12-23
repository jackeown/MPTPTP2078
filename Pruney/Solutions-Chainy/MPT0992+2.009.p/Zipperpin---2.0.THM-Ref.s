%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HFsn0rxdLc

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:35 EST 2020

% Result     : Theorem 10.50s
% Output     : Refutation 10.59s
% Verified   : 
% Statistics : Number of formulae       :  213 (2881 expanded)
%              Number of leaves         :   42 ( 800 expanded)
%              Depth                    :   31
%              Number of atoms          : 1656 (43762 expanded)
%              Number of equality atoms :  150 (3506 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X40 @ X41 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k2_partfun1 @ X44 @ X45 @ X43 @ X46 )
        = ( k7_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('13',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','11','12'])).

thf('14',plain,(
    r1_tarski @ sk_C @ sk_A ),
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

thf('15',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('31',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('32',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('37',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','37'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('41',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('42',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('44',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('47',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','37'])).

thf('49',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('50',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( v5_relat_1 @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ k1_xboole_0 )
        | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('59',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('60',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('64',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('65',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('68',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k2_partfun1 @ X44 @ X45 @ X43 @ X46 )
        = ( k7_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('70',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
          = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
        | ~ ( v1_funct_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('72',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('73',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('77',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','75','78'])).

thf('80',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('81',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('83',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('84',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('85',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('86',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','75','78'])).

thf('87',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('89',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('90',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
        = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('94',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('97',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('99',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
        = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('101',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('103',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('104',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('107',plain,(
    ! [X31: $i] :
      ( zip_tseitin_0 @ X31 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['105','107'])).

thf('109',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','108'])).

thf('110',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','109'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','110'])).

thf('112',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('113',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','108'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['32','42','47','79','80','81','82','83','84','85','86','87','116'])).

thf('118',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('119',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['117','118'])).

thf('120',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','119'])).

thf('121',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['27','120'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('122',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('129',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('131',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('133',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['131','132'])).

thf(t99_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('134',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) @ ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t99_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf('138',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('139',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['137','138'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('140',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X47 ) @ X48 )
      | ( v1_funct_2 @ X47 @ ( k1_relat_1 @ X47 ) @ X48 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('144',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('149',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('150',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('152',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('157',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['141','154','157'])).

thf('159',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['126','158'])).

thf('160',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','159'])).

thf('161',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','125'])).

thf('162',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('163',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X47 ) @ X48 )
      | ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X47 ) @ X48 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('166',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('167',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['164','165','166'])).

thf('168',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['161','167'])).

thf('169',plain,(
    $false ),
    inference(demod,[status(thm)],['160','168'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HFsn0rxdLc
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:23:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 10.50/10.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.50/10.77  % Solved by: fo/fo7.sh
% 10.50/10.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.50/10.77  % done 7203 iterations in 10.318s
% 10.50/10.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.50/10.77  % SZS output start Refutation
% 10.50/10.77  thf(sk_A_type, type, sk_A: $i).
% 10.50/10.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 10.50/10.77  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 10.50/10.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 10.50/10.77  thf(sk_D_type, type, sk_D: $i).
% 10.50/10.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.50/10.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 10.50/10.77  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 10.50/10.77  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 10.50/10.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 10.50/10.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.50/10.77  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 10.50/10.77  thf(sk_B_type, type, sk_B: $i).
% 10.50/10.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.50/10.77  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 10.50/10.77  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 10.50/10.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 10.50/10.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.50/10.77  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 10.50/10.77  thf(sk_C_type, type, sk_C: $i).
% 10.50/10.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.50/10.77  thf(t38_funct_2, conjecture,
% 10.50/10.77    (![A:$i,B:$i,C:$i,D:$i]:
% 10.50/10.77     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 10.50/10.77         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.50/10.77       ( ( r1_tarski @ C @ A ) =>
% 10.50/10.77         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 10.50/10.77           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 10.50/10.77             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 10.50/10.77             ( m1_subset_1 @
% 10.50/10.77               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 10.50/10.77               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 10.50/10.77  thf(zf_stmt_0, negated_conjecture,
% 10.50/10.77    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 10.50/10.77        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 10.50/10.77            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.50/10.77          ( ( r1_tarski @ C @ A ) =>
% 10.50/10.77            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 10.50/10.77              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 10.50/10.77                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 10.50/10.77                ( m1_subset_1 @
% 10.50/10.77                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 10.50/10.77                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 10.50/10.77    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 10.50/10.77  thf('0', plain,
% 10.50/10.77      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 10.50/10.77        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 10.50/10.77             sk_B)
% 10.50/10.77        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 10.50/10.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.50/10.77  thf('1', plain,
% 10.50/10.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.50/10.77  thf(dt_k2_partfun1, axiom,
% 10.50/10.77    (![A:$i,B:$i,C:$i,D:$i]:
% 10.50/10.77     ( ( ( v1_funct_1 @ C ) & 
% 10.50/10.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.50/10.77       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 10.50/10.77         ( m1_subset_1 @
% 10.50/10.77           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 10.50/10.77           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 10.50/10.77  thf('2', plain,
% 10.50/10.77      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 10.50/10.77         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 10.50/10.77          | ~ (v1_funct_1 @ X39)
% 10.50/10.77          | (v1_funct_1 @ (k2_partfun1 @ X40 @ X41 @ X39 @ X42)))),
% 10.50/10.77      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 10.50/10.77  thf('3', plain,
% 10.50/10.77      (![X0 : $i]:
% 10.50/10.77         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 10.50/10.77          | ~ (v1_funct_1 @ sk_D))),
% 10.50/10.77      inference('sup-', [status(thm)], ['1', '2'])).
% 10.50/10.77  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.50/10.77  thf('5', plain,
% 10.50/10.77      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 10.50/10.77      inference('demod', [status(thm)], ['3', '4'])).
% 10.50/10.77  thf('6', plain,
% 10.50/10.77      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 10.50/10.77        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 10.50/10.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 10.50/10.77      inference('demod', [status(thm)], ['0', '5'])).
% 10.50/10.77  thf('7', plain,
% 10.50/10.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.50/10.77  thf(redefinition_k2_partfun1, axiom,
% 10.50/10.77    (![A:$i,B:$i,C:$i,D:$i]:
% 10.50/10.77     ( ( ( v1_funct_1 @ C ) & 
% 10.50/10.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.50/10.77       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 10.50/10.77  thf('8', plain,
% 10.50/10.77      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 10.50/10.77         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 10.50/10.77          | ~ (v1_funct_1 @ X43)
% 10.50/10.77          | ((k2_partfun1 @ X44 @ X45 @ X43 @ X46) = (k7_relat_1 @ X43 @ X46)))),
% 10.50/10.77      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 10.50/10.77  thf('9', plain,
% 10.50/10.77      (![X0 : $i]:
% 10.50/10.77         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 10.50/10.77          | ~ (v1_funct_1 @ sk_D))),
% 10.50/10.77      inference('sup-', [status(thm)], ['7', '8'])).
% 10.50/10.77  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.50/10.77  thf('11', plain,
% 10.50/10.77      (![X0 : $i]:
% 10.50/10.77         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 10.50/10.77      inference('demod', [status(thm)], ['9', '10'])).
% 10.50/10.77  thf('12', plain,
% 10.50/10.77      (![X0 : $i]:
% 10.50/10.77         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 10.50/10.77      inference('demod', [status(thm)], ['9', '10'])).
% 10.50/10.77  thf('13', plain,
% 10.50/10.77      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 10.50/10.77        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 10.50/10.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 10.50/10.77      inference('demod', [status(thm)], ['6', '11', '12'])).
% 10.50/10.77  thf('14', plain, ((r1_tarski @ sk_C @ sk_A)),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.50/10.77  thf(d1_funct_2, axiom,
% 10.50/10.77    (![A:$i,B:$i,C:$i]:
% 10.50/10.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.50/10.77       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.50/10.77           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 10.50/10.77             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 10.50/10.77         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.50/10.77           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 10.50/10.77             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 10.50/10.77  thf(zf_stmt_1, axiom,
% 10.50/10.77    (![B:$i,A:$i]:
% 10.50/10.77     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.50/10.77       ( zip_tseitin_0 @ B @ A ) ))).
% 10.50/10.77  thf('15', plain,
% 10.50/10.77      (![X31 : $i, X32 : $i]:
% 10.50/10.77         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.50/10.77  thf('16', plain,
% 10.50/10.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.50/10.77  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 10.50/10.77  thf(zf_stmt_3, axiom,
% 10.50/10.77    (![C:$i,B:$i,A:$i]:
% 10.50/10.77     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 10.50/10.77       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 10.50/10.77  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 10.50/10.77  thf(zf_stmt_5, axiom,
% 10.50/10.77    (![A:$i,B:$i,C:$i]:
% 10.50/10.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.50/10.77       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 10.50/10.77         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.50/10.77           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 10.50/10.77             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 10.50/10.77  thf('17', plain,
% 10.50/10.77      (![X36 : $i, X37 : $i, X38 : $i]:
% 10.50/10.77         (~ (zip_tseitin_0 @ X36 @ X37)
% 10.50/10.77          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 10.50/10.77          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.50/10.77  thf('18', plain,
% 10.50/10.77      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 10.50/10.77      inference('sup-', [status(thm)], ['16', '17'])).
% 10.50/10.77  thf('19', plain,
% 10.50/10.77      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 10.50/10.77      inference('sup-', [status(thm)], ['15', '18'])).
% 10.50/10.77  thf('20', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.50/10.77  thf('21', plain,
% 10.50/10.77      (![X33 : $i, X34 : $i, X35 : $i]:
% 10.50/10.77         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 10.50/10.77          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 10.50/10.77          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.50/10.77  thf('22', plain,
% 10.50/10.77      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 10.50/10.77        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 10.50/10.77      inference('sup-', [status(thm)], ['20', '21'])).
% 10.50/10.77  thf('23', plain,
% 10.50/10.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.50/10.77  thf(redefinition_k1_relset_1, axiom,
% 10.50/10.77    (![A:$i,B:$i,C:$i]:
% 10.50/10.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.50/10.77       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 10.50/10.77  thf('24', plain,
% 10.50/10.77      (![X28 : $i, X29 : $i, X30 : $i]:
% 10.50/10.77         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 10.50/10.77          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 10.50/10.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.50/10.77  thf('25', plain,
% 10.50/10.77      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 10.50/10.77      inference('sup-', [status(thm)], ['23', '24'])).
% 10.50/10.77  thf('26', plain,
% 10.50/10.77      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.50/10.77      inference('demod', [status(thm)], ['22', '25'])).
% 10.50/10.77  thf('27', plain,
% 10.50/10.77      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.50/10.77      inference('sup-', [status(thm)], ['19', '26'])).
% 10.50/10.77  thf('28', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.50/10.77  thf('29', plain,
% 10.50/10.77      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 10.50/10.77      inference('split', [status(esa)], ['28'])).
% 10.50/10.77  thf('30', plain,
% 10.50/10.77      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('split', [status(esa)], ['28'])).
% 10.50/10.77  thf('31', plain,
% 10.50/10.77      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 10.50/10.77        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 10.50/10.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 10.50/10.77      inference('demod', [status(thm)], ['0', '5'])).
% 10.50/10.77  thf('32', plain,
% 10.50/10.77      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 10.50/10.77            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 10.50/10.77         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 10.50/10.77              sk_B)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['30', '31'])).
% 10.50/10.77  thf('33', plain,
% 10.50/10.77      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('split', [status(esa)], ['28'])).
% 10.50/10.77  thf('34', plain,
% 10.50/10.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.50/10.77  thf('35', plain,
% 10.50/10.77      (((m1_subset_1 @ sk_D @ 
% 10.50/10.77         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup+', [status(thm)], ['33', '34'])).
% 10.50/10.77  thf(t113_zfmisc_1, axiom,
% 10.50/10.77    (![A:$i,B:$i]:
% 10.50/10.77     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 10.50/10.77       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 10.50/10.77  thf('36', plain,
% 10.50/10.77      (![X5 : $i, X6 : $i]:
% 10.50/10.77         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 10.50/10.77      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 10.50/10.77  thf('37', plain,
% 10.50/10.77      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 10.50/10.77      inference('simplify', [status(thm)], ['36'])).
% 10.50/10.77  thf('38', plain,
% 10.50/10.77      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('demod', [status(thm)], ['35', '37'])).
% 10.50/10.77  thf(t3_subset, axiom,
% 10.50/10.77    (![A:$i,B:$i]:
% 10.50/10.77     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 10.50/10.77  thf('39', plain,
% 10.50/10.77      (![X7 : $i, X8 : $i]:
% 10.50/10.77         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 10.50/10.77      inference('cnf', [status(esa)], [t3_subset])).
% 10.50/10.77  thf('40', plain,
% 10.50/10.77      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['38', '39'])).
% 10.50/10.77  thf(t3_xboole_1, axiom,
% 10.50/10.77    (![A:$i]:
% 10.50/10.77     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 10.50/10.77  thf('41', plain,
% 10.50/10.77      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 10.50/10.77      inference('cnf', [status(esa)], [t3_xboole_1])).
% 10.50/10.77  thf('42', plain,
% 10.50/10.77      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['40', '41'])).
% 10.50/10.77  thf('43', plain,
% 10.50/10.77      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('split', [status(esa)], ['28'])).
% 10.50/10.77  thf('44', plain, ((r1_tarski @ sk_C @ sk_A)),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.50/10.77  thf('45', plain,
% 10.50/10.77      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup+', [status(thm)], ['43', '44'])).
% 10.50/10.77  thf('46', plain,
% 10.50/10.77      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 10.50/10.77      inference('cnf', [status(esa)], [t3_xboole_1])).
% 10.50/10.77  thf('47', plain,
% 10.50/10.77      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['45', '46'])).
% 10.50/10.77  thf('48', plain,
% 10.50/10.77      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('demod', [status(thm)], ['35', '37'])).
% 10.50/10.77  thf('49', plain,
% 10.50/10.77      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['40', '41'])).
% 10.50/10.77  thf('50', plain,
% 10.50/10.77      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('demod', [status(thm)], ['48', '49'])).
% 10.50/10.77  thf('51', plain,
% 10.50/10.77      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 10.50/10.77      inference('simplify', [status(thm)], ['36'])).
% 10.50/10.77  thf(cc2_relset_1, axiom,
% 10.50/10.77    (![A:$i,B:$i,C:$i]:
% 10.50/10.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.50/10.77       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 10.50/10.77  thf('52', plain,
% 10.50/10.77      (![X25 : $i, X26 : $i, X27 : $i]:
% 10.50/10.77         ((v5_relat_1 @ X25 @ X27)
% 10.50/10.77          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 10.50/10.77      inference('cnf', [status(esa)], [cc2_relset_1])).
% 10.50/10.77  thf('53', plain,
% 10.50/10.77      (![X0 : $i, X1 : $i]:
% 10.50/10.77         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 10.50/10.77          | (v5_relat_1 @ X1 @ X0))),
% 10.50/10.77      inference('sup-', [status(thm)], ['51', '52'])).
% 10.50/10.77  thf('54', plain,
% 10.50/10.77      ((![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['50', '53'])).
% 10.50/10.77  thf(d19_relat_1, axiom,
% 10.50/10.77    (![A:$i,B:$i]:
% 10.50/10.77     ( ( v1_relat_1 @ B ) =>
% 10.50/10.77       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 10.50/10.77  thf('55', plain,
% 10.50/10.77      (![X12 : $i, X13 : $i]:
% 10.50/10.77         (~ (v5_relat_1 @ X12 @ X13)
% 10.50/10.77          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 10.50/10.77          | ~ (v1_relat_1 @ X12))),
% 10.50/10.77      inference('cnf', [status(esa)], [d19_relat_1])).
% 10.50/10.77  thf('56', plain,
% 10.50/10.77      ((![X0 : $i]:
% 10.50/10.77          (~ (v1_relat_1 @ k1_xboole_0)
% 10.50/10.77           | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['54', '55'])).
% 10.50/10.77  thf('57', plain,
% 10.50/10.77      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['40', '41'])).
% 10.50/10.77  thf('58', plain,
% 10.50/10.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.50/10.77  thf(cc1_relset_1, axiom,
% 10.50/10.77    (![A:$i,B:$i,C:$i]:
% 10.50/10.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.50/10.77       ( v1_relat_1 @ C ) ))).
% 10.50/10.77  thf('59', plain,
% 10.50/10.77      (![X22 : $i, X23 : $i, X24 : $i]:
% 10.50/10.77         ((v1_relat_1 @ X22)
% 10.50/10.77          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 10.50/10.77      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.50/10.77  thf('60', plain, ((v1_relat_1 @ sk_D)),
% 10.50/10.77      inference('sup-', [status(thm)], ['58', '59'])).
% 10.50/10.77  thf('61', plain,
% 10.50/10.77      (((v1_relat_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup+', [status(thm)], ['57', '60'])).
% 10.50/10.77  thf('62', plain,
% 10.50/10.77      ((![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('demod', [status(thm)], ['56', '61'])).
% 10.50/10.77  thf('63', plain,
% 10.50/10.77      ((![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('demod', [status(thm)], ['56', '61'])).
% 10.50/10.77  thf('64', plain,
% 10.50/10.77      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 10.50/10.77      inference('cnf', [status(esa)], [t3_xboole_1])).
% 10.50/10.77  thf('65', plain,
% 10.50/10.77      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['63', '64'])).
% 10.50/10.77  thf('66', plain,
% 10.50/10.77      ((![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('demod', [status(thm)], ['62', '65'])).
% 10.50/10.77  thf('67', plain,
% 10.50/10.77      (![X7 : $i, X9 : $i]:
% 10.50/10.77         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 10.50/10.77      inference('cnf', [status(esa)], [t3_subset])).
% 10.50/10.77  thf('68', plain,
% 10.50/10.77      ((![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['66', '67'])).
% 10.50/10.77  thf('69', plain,
% 10.50/10.77      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 10.50/10.77         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 10.50/10.77          | ~ (v1_funct_1 @ X43)
% 10.50/10.77          | ((k2_partfun1 @ X44 @ X45 @ X43 @ X46) = (k7_relat_1 @ X43 @ X46)))),
% 10.50/10.77      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 10.50/10.77  thf('70', plain,
% 10.50/10.77      ((![X0 : $i, X1 : $i, X2 : $i]:
% 10.50/10.77          (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 10.50/10.77             = (k7_relat_1 @ k1_xboole_0 @ X2))
% 10.50/10.77           | ~ (v1_funct_1 @ k1_xboole_0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['68', '69'])).
% 10.50/10.77  thf('71', plain,
% 10.50/10.77      (((v1_relat_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup+', [status(thm)], ['57', '60'])).
% 10.50/10.77  thf(t88_relat_1, axiom,
% 10.50/10.77    (![A:$i,B:$i]:
% 10.50/10.77     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 10.50/10.77  thf('72', plain,
% 10.50/10.77      (![X16 : $i, X17 : $i]:
% 10.50/10.77         ((r1_tarski @ (k7_relat_1 @ X16 @ X17) @ X16) | ~ (v1_relat_1 @ X16))),
% 10.50/10.77      inference('cnf', [status(esa)], [t88_relat_1])).
% 10.50/10.77  thf('73', plain,
% 10.50/10.77      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 10.50/10.77      inference('cnf', [status(esa)], [t3_xboole_1])).
% 10.50/10.77  thf('74', plain,
% 10.50/10.77      (![X0 : $i]:
% 10.50/10.77         (~ (v1_relat_1 @ k1_xboole_0)
% 10.50/10.77          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 10.50/10.77      inference('sup-', [status(thm)], ['72', '73'])).
% 10.50/10.77  thf('75', plain,
% 10.50/10.77      ((![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['71', '74'])).
% 10.50/10.77  thf('76', plain,
% 10.50/10.77      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['40', '41'])).
% 10.50/10.77  thf('77', plain, ((v1_funct_1 @ sk_D)),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.50/10.77  thf('78', plain,
% 10.50/10.77      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup+', [status(thm)], ['76', '77'])).
% 10.50/10.77  thf('79', plain,
% 10.50/10.77      ((![X0 : $i, X1 : $i, X2 : $i]:
% 10.50/10.77          ((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('demod', [status(thm)], ['70', '75', '78'])).
% 10.50/10.77  thf('80', plain,
% 10.50/10.77      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['45', '46'])).
% 10.50/10.77  thf('81', plain,
% 10.50/10.77      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 10.50/10.77      inference('simplify', [status(thm)], ['36'])).
% 10.50/10.77  thf('82', plain,
% 10.50/10.77      ((![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['66', '67'])).
% 10.50/10.77  thf('83', plain,
% 10.50/10.77      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('split', [status(esa)], ['28'])).
% 10.50/10.77  thf('84', plain,
% 10.50/10.77      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['40', '41'])).
% 10.50/10.77  thf('85', plain,
% 10.50/10.77      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['45', '46'])).
% 10.50/10.77  thf('86', plain,
% 10.50/10.77      ((![X0 : $i, X1 : $i, X2 : $i]:
% 10.50/10.77          ((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('demod', [status(thm)], ['70', '75', '78'])).
% 10.50/10.77  thf('87', plain,
% 10.50/10.77      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['45', '46'])).
% 10.50/10.77  thf('88', plain,
% 10.50/10.77      ((![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['66', '67'])).
% 10.50/10.77  thf('89', plain,
% 10.50/10.77      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 10.50/10.77      inference('simplify', [status(thm)], ['36'])).
% 10.50/10.77  thf('90', plain,
% 10.50/10.77      (![X28 : $i, X29 : $i, X30 : $i]:
% 10.50/10.77         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 10.50/10.77          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 10.50/10.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.50/10.77  thf('91', plain,
% 10.50/10.77      (![X0 : $i, X1 : $i]:
% 10.50/10.77         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 10.50/10.77          | ((k1_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k1_relat_1 @ X1)))),
% 10.50/10.77      inference('sup-', [status(thm)], ['89', '90'])).
% 10.50/10.77  thf('92', plain,
% 10.50/10.77      ((![X0 : $i]:
% 10.50/10.77          ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 10.50/10.77            = (k1_relat_1 @ k1_xboole_0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['88', '91'])).
% 10.50/10.77  thf('93', plain,
% 10.50/10.77      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('split', [status(esa)], ['28'])).
% 10.50/10.77  thf('94', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.50/10.77  thf('95', plain,
% 10.50/10.77      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup+', [status(thm)], ['93', '94'])).
% 10.50/10.77  thf('96', plain,
% 10.50/10.77      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['40', '41'])).
% 10.50/10.77  thf('97', plain,
% 10.50/10.77      (((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('demod', [status(thm)], ['95', '96'])).
% 10.50/10.77  thf('98', plain,
% 10.50/10.77      (![X33 : $i, X34 : $i, X35 : $i]:
% 10.50/10.77         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 10.50/10.77          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 10.50/10.77          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.50/10.77  thf('99', plain,
% 10.50/10.77      (((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0)
% 10.50/10.77         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0))))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['97', '98'])).
% 10.50/10.77  thf('100', plain,
% 10.50/10.77      ((![X0 : $i]:
% 10.50/10.77          ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 10.50/10.77            = (k1_relat_1 @ k1_xboole_0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['88', '91'])).
% 10.50/10.77  thf('101', plain,
% 10.50/10.77      (((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0)
% 10.50/10.77         | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('demod', [status(thm)], ['99', '100'])).
% 10.50/10.77  thf('102', plain,
% 10.50/10.77      ((![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['66', '67'])).
% 10.50/10.77  thf('103', plain,
% 10.50/10.77      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 10.50/10.77      inference('simplify', [status(thm)], ['36'])).
% 10.50/10.77  thf('104', plain,
% 10.50/10.77      (![X36 : $i, X37 : $i, X38 : $i]:
% 10.50/10.77         (~ (zip_tseitin_0 @ X36 @ X37)
% 10.50/10.77          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 10.50/10.77          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.50/10.77  thf('105', plain,
% 10.50/10.77      (![X0 : $i, X1 : $i]:
% 10.50/10.77         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 10.50/10.77          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 10.50/10.77          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 10.50/10.77      inference('sup-', [status(thm)], ['103', '104'])).
% 10.50/10.77  thf('106', plain,
% 10.50/10.77      (![X31 : $i, X32 : $i]:
% 10.50/10.77         ((zip_tseitin_0 @ X31 @ X32) | ((X32) != (k1_xboole_0)))),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.50/10.77  thf('107', plain, (![X31 : $i]: (zip_tseitin_0 @ X31 @ k1_xboole_0)),
% 10.50/10.77      inference('simplify', [status(thm)], ['106'])).
% 10.50/10.77  thf('108', plain,
% 10.50/10.77      (![X0 : $i, X1 : $i]:
% 10.50/10.77         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 10.50/10.77          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 10.50/10.77      inference('demod', [status(thm)], ['105', '107'])).
% 10.50/10.77  thf('109', plain,
% 10.50/10.77      ((![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['102', '108'])).
% 10.50/10.77  thf('110', plain,
% 10.50/10.77      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('demod', [status(thm)], ['101', '109'])).
% 10.50/10.77  thf('111', plain,
% 10.50/10.77      ((![X0 : $i]:
% 10.50/10.77          ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('demod', [status(thm)], ['92', '110'])).
% 10.50/10.77  thf('112', plain,
% 10.50/10.77      (![X33 : $i, X34 : $i, X35 : $i]:
% 10.50/10.77         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 10.50/10.77          | (v1_funct_2 @ X35 @ X33 @ X34)
% 10.50/10.77          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 10.50/10.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.50/10.77  thf('113', plain,
% 10.50/10.77      ((![X0 : $i]:
% 10.50/10.77          (((k1_xboole_0) != (k1_xboole_0))
% 10.50/10.77           | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 10.50/10.77           | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['111', '112'])).
% 10.50/10.77  thf('114', plain,
% 10.50/10.77      ((![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('sup-', [status(thm)], ['102', '108'])).
% 10.50/10.77  thf('115', plain,
% 10.50/10.77      ((![X0 : $i]:
% 10.50/10.77          (((k1_xboole_0) != (k1_xboole_0))
% 10.50/10.77           | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('demod', [status(thm)], ['113', '114'])).
% 10.50/10.77  thf('116', plain,
% 10.50/10.77      ((![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))
% 10.50/10.77         <= ((((sk_A) = (k1_xboole_0))))),
% 10.50/10.77      inference('simplify', [status(thm)], ['115'])).
% 10.50/10.77  thf('117', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 10.50/10.77      inference('demod', [status(thm)],
% 10.50/10.77                ['32', '42', '47', '79', '80', '81', '82', '83', '84', '85', 
% 10.50/10.77                 '86', '87', '116'])).
% 10.50/10.77  thf('118', plain,
% 10.50/10.77      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 10.50/10.77      inference('split', [status(esa)], ['28'])).
% 10.50/10.77  thf('119', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 10.50/10.77      inference('sat_resolution*', [status(thm)], ['117', '118'])).
% 10.50/10.77  thf('120', plain, (((sk_B) != (k1_xboole_0))),
% 10.50/10.77      inference('simpl_trail', [status(thm)], ['29', '119'])).
% 10.50/10.77  thf('121', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 10.50/10.77      inference('simplify_reflect-', [status(thm)], ['27', '120'])).
% 10.50/10.77  thf(t91_relat_1, axiom,
% 10.50/10.77    (![A:$i,B:$i]:
% 10.50/10.77     ( ( v1_relat_1 @ B ) =>
% 10.50/10.77       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 10.50/10.77         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 10.50/10.77  thf('122', plain,
% 10.50/10.77      (![X18 : $i, X19 : $i]:
% 10.50/10.77         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 10.50/10.77          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 10.50/10.77          | ~ (v1_relat_1 @ X19))),
% 10.50/10.77      inference('cnf', [status(esa)], [t91_relat_1])).
% 10.50/10.77  thf('123', plain,
% 10.50/10.77      (![X0 : $i]:
% 10.50/10.77         (~ (r1_tarski @ X0 @ sk_A)
% 10.50/10.77          | ~ (v1_relat_1 @ sk_D)
% 10.59/10.77          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 10.59/10.77      inference('sup-', [status(thm)], ['121', '122'])).
% 10.59/10.77  thf('124', plain, ((v1_relat_1 @ sk_D)),
% 10.59/10.77      inference('sup-', [status(thm)], ['58', '59'])).
% 10.59/10.77  thf('125', plain,
% 10.59/10.77      (![X0 : $i]:
% 10.59/10.77         (~ (r1_tarski @ X0 @ sk_A)
% 10.59/10.77          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 10.59/10.77      inference('demod', [status(thm)], ['123', '124'])).
% 10.59/10.77  thf('126', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 10.59/10.77      inference('sup-', [status(thm)], ['14', '125'])).
% 10.59/10.77  thf('127', plain,
% 10.59/10.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.59/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.59/10.77  thf('128', plain,
% 10.59/10.77      (![X25 : $i, X26 : $i, X27 : $i]:
% 10.59/10.77         ((v5_relat_1 @ X25 @ X27)
% 10.59/10.77          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 10.59/10.77      inference('cnf', [status(esa)], [cc2_relset_1])).
% 10.59/10.77  thf('129', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 10.59/10.77      inference('sup-', [status(thm)], ['127', '128'])).
% 10.59/10.77  thf('130', plain,
% 10.59/10.77      (![X12 : $i, X13 : $i]:
% 10.59/10.77         (~ (v5_relat_1 @ X12 @ X13)
% 10.59/10.77          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 10.59/10.77          | ~ (v1_relat_1 @ X12))),
% 10.59/10.77      inference('cnf', [status(esa)], [d19_relat_1])).
% 10.59/10.77  thf('131', plain,
% 10.59/10.77      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 10.59/10.77      inference('sup-', [status(thm)], ['129', '130'])).
% 10.59/10.77  thf('132', plain, ((v1_relat_1 @ sk_D)),
% 10.59/10.77      inference('sup-', [status(thm)], ['58', '59'])).
% 10.59/10.77  thf('133', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 10.59/10.77      inference('demod', [status(thm)], ['131', '132'])).
% 10.59/10.77  thf(t99_relat_1, axiom,
% 10.59/10.77    (![A:$i,B:$i]:
% 10.59/10.77     ( ( v1_relat_1 @ B ) =>
% 10.59/10.77       ( r1_tarski @
% 10.59/10.77         ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ))).
% 10.59/10.77  thf('134', plain,
% 10.59/10.77      (![X20 : $i, X21 : $i]:
% 10.59/10.77         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) @ 
% 10.59/10.77           (k2_relat_1 @ X20))
% 10.59/10.77          | ~ (v1_relat_1 @ X20))),
% 10.59/10.77      inference('cnf', [status(esa)], [t99_relat_1])).
% 10.59/10.77  thf(t1_xboole_1, axiom,
% 10.59/10.77    (![A:$i,B:$i,C:$i]:
% 10.59/10.77     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 10.59/10.77       ( r1_tarski @ A @ C ) ))).
% 10.59/10.77  thf('135', plain,
% 10.59/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.59/10.77         (~ (r1_tarski @ X0 @ X1)
% 10.59/10.77          | ~ (r1_tarski @ X1 @ X2)
% 10.59/10.77          | (r1_tarski @ X0 @ X2))),
% 10.59/10.77      inference('cnf', [status(esa)], [t1_xboole_1])).
% 10.59/10.77  thf('136', plain,
% 10.59/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.59/10.77         (~ (v1_relat_1 @ X0)
% 10.59/10.77          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 10.59/10.77          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X2))),
% 10.59/10.77      inference('sup-', [status(thm)], ['134', '135'])).
% 10.59/10.77  thf('137', plain,
% 10.59/10.77      (![X0 : $i]:
% 10.59/10.77         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)
% 10.59/10.77          | ~ (v1_relat_1 @ sk_D))),
% 10.59/10.77      inference('sup-', [status(thm)], ['133', '136'])).
% 10.59/10.77  thf('138', plain, ((v1_relat_1 @ sk_D)),
% 10.59/10.77      inference('sup-', [status(thm)], ['58', '59'])).
% 10.59/10.77  thf('139', plain,
% 10.59/10.77      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 10.59/10.77      inference('demod', [status(thm)], ['137', '138'])).
% 10.59/10.77  thf(t4_funct_2, axiom,
% 10.59/10.77    (![A:$i,B:$i]:
% 10.59/10.77     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 10.59/10.77       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 10.59/10.77         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 10.59/10.77           ( m1_subset_1 @
% 10.59/10.77             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 10.59/10.77  thf('140', plain,
% 10.59/10.77      (![X47 : $i, X48 : $i]:
% 10.59/10.77         (~ (r1_tarski @ (k2_relat_1 @ X47) @ X48)
% 10.59/10.77          | (v1_funct_2 @ X47 @ (k1_relat_1 @ X47) @ X48)
% 10.59/10.77          | ~ (v1_funct_1 @ X47)
% 10.59/10.77          | ~ (v1_relat_1 @ X47))),
% 10.59/10.77      inference('cnf', [status(esa)], [t4_funct_2])).
% 10.59/10.77  thf('141', plain,
% 10.59/10.77      (![X0 : $i]:
% 10.59/10.77         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 10.59/10.77          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 10.59/10.77          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 10.59/10.77             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 10.59/10.77      inference('sup-', [status(thm)], ['139', '140'])).
% 10.59/10.77  thf('142', plain,
% 10.59/10.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.59/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.59/10.77  thf('143', plain,
% 10.59/10.77      (![X7 : $i, X8 : $i]:
% 10.59/10.77         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 10.59/10.77      inference('cnf', [status(esa)], [t3_subset])).
% 10.59/10.77  thf('144', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 10.59/10.77      inference('sup-', [status(thm)], ['142', '143'])).
% 10.59/10.77  thf('145', plain,
% 10.59/10.77      (![X16 : $i, X17 : $i]:
% 10.59/10.77         ((r1_tarski @ (k7_relat_1 @ X16 @ X17) @ X16) | ~ (v1_relat_1 @ X16))),
% 10.59/10.77      inference('cnf', [status(esa)], [t88_relat_1])).
% 10.59/10.77  thf('146', plain,
% 10.59/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.59/10.77         (~ (r1_tarski @ X0 @ X1)
% 10.59/10.77          | ~ (r1_tarski @ X1 @ X2)
% 10.59/10.77          | (r1_tarski @ X0 @ X2))),
% 10.59/10.77      inference('cnf', [status(esa)], [t1_xboole_1])).
% 10.59/10.77  thf('147', plain,
% 10.59/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.59/10.77         (~ (v1_relat_1 @ X0)
% 10.59/10.77          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 10.59/10.77          | ~ (r1_tarski @ X0 @ X2))),
% 10.59/10.77      inference('sup-', [status(thm)], ['145', '146'])).
% 10.59/10.77  thf('148', plain,
% 10.59/10.77      (![X0 : $i]:
% 10.59/10.77         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 10.59/10.77          | ~ (v1_relat_1 @ sk_D))),
% 10.59/10.77      inference('sup-', [status(thm)], ['144', '147'])).
% 10.59/10.77  thf('149', plain, ((v1_relat_1 @ sk_D)),
% 10.59/10.77      inference('sup-', [status(thm)], ['58', '59'])).
% 10.59/10.77  thf('150', plain,
% 10.59/10.77      (![X0 : $i]:
% 10.59/10.77         (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 10.59/10.77      inference('demod', [status(thm)], ['148', '149'])).
% 10.59/10.77  thf('151', plain,
% 10.59/10.77      (![X7 : $i, X9 : $i]:
% 10.59/10.77         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 10.59/10.77      inference('cnf', [status(esa)], [t3_subset])).
% 10.59/10.77  thf('152', plain,
% 10.59/10.77      (![X0 : $i]:
% 10.59/10.77         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 10.59/10.77          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.59/10.77      inference('sup-', [status(thm)], ['150', '151'])).
% 10.59/10.77  thf('153', plain,
% 10.59/10.77      (![X22 : $i, X23 : $i, X24 : $i]:
% 10.59/10.77         ((v1_relat_1 @ X22)
% 10.59/10.77          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 10.59/10.77      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.59/10.77  thf('154', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 10.59/10.77      inference('sup-', [status(thm)], ['152', '153'])).
% 10.59/10.77  thf('155', plain,
% 10.59/10.77      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 10.59/10.77      inference('demod', [status(thm)], ['3', '4'])).
% 10.59/10.77  thf('156', plain,
% 10.59/10.77      (![X0 : $i]:
% 10.59/10.77         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 10.59/10.77      inference('demod', [status(thm)], ['9', '10'])).
% 10.59/10.77  thf('157', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 10.59/10.77      inference('demod', [status(thm)], ['155', '156'])).
% 10.59/10.77  thf('158', plain,
% 10.59/10.77      (![X0 : $i]:
% 10.59/10.77         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 10.59/10.77          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 10.59/10.77      inference('demod', [status(thm)], ['141', '154', '157'])).
% 10.59/10.77  thf('159', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 10.59/10.77      inference('sup+', [status(thm)], ['126', '158'])).
% 10.59/10.77  thf('160', plain,
% 10.59/10.77      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 10.59/10.77          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 10.59/10.77      inference('demod', [status(thm)], ['13', '159'])).
% 10.59/10.77  thf('161', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 10.59/10.77      inference('sup-', [status(thm)], ['14', '125'])).
% 10.59/10.77  thf('162', plain,
% 10.59/10.77      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 10.59/10.77      inference('demod', [status(thm)], ['137', '138'])).
% 10.59/10.77  thf('163', plain,
% 10.59/10.77      (![X47 : $i, X48 : $i]:
% 10.59/10.77         (~ (r1_tarski @ (k2_relat_1 @ X47) @ X48)
% 10.59/10.77          | (m1_subset_1 @ X47 @ 
% 10.59/10.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X47) @ X48)))
% 10.59/10.77          | ~ (v1_funct_1 @ X47)
% 10.59/10.77          | ~ (v1_relat_1 @ X47))),
% 10.59/10.77      inference('cnf', [status(esa)], [t4_funct_2])).
% 10.59/10.77  thf('164', plain,
% 10.59/10.77      (![X0 : $i]:
% 10.59/10.77         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 10.59/10.77          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 10.59/10.77          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 10.59/10.77             (k1_zfmisc_1 @ 
% 10.59/10.77              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 10.59/10.77      inference('sup-', [status(thm)], ['162', '163'])).
% 10.59/10.77  thf('165', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 10.59/10.77      inference('sup-', [status(thm)], ['152', '153'])).
% 10.59/10.77  thf('166', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 10.59/10.77      inference('demod', [status(thm)], ['155', '156'])).
% 10.59/10.77  thf('167', plain,
% 10.59/10.77      (![X0 : $i]:
% 10.59/10.77         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 10.59/10.77          (k1_zfmisc_1 @ 
% 10.59/10.77           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 10.59/10.77      inference('demod', [status(thm)], ['164', '165', '166'])).
% 10.59/10.77  thf('168', plain,
% 10.59/10.77      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 10.59/10.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 10.59/10.77      inference('sup+', [status(thm)], ['161', '167'])).
% 10.59/10.77  thf('169', plain, ($false), inference('demod', [status(thm)], ['160', '168'])).
% 10.59/10.77  
% 10.59/10.77  % SZS output end Refutation
% 10.59/10.77  
% 10.59/10.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
