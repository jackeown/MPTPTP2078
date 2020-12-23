%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MmBEF2DdJZ

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:39 EST 2020

% Result     : Theorem 15.39s
% Output     : Refutation 15.39s
% Verified   : 
% Statistics : Number of formulae       :  212 (1047 expanded)
%              Number of leaves         :   40 ( 302 expanded)
%              Depth                    :   24
%              Number of atoms          : 1786 (19254 expanded)
%              Number of equality atoms :  146 (1216 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ( ( k2_partfun1 @ X37 @ X38 @ X36 @ X39 )
        = ( k7_relat_1 @ X36 @ X39 ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X33 @ X34 @ X32 @ X35 ) ) ) ),
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

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('18',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('41',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('48',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('51',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ( ( k2_partfun1 @ X37 @ X38 @ X36 @ X39 )
        = ( k7_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k2_partfun1 @ k1_xboole_0 @ X0 @ X1 @ X2 )
        = ( k7_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_funct_1 @ sk_D )
        | ( ( k2_partfun1 @ k1_xboole_0 @ X1 @ sk_D @ X0 )
          = ( k7_relat_1 @ sk_D @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','48'])).

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('57',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('58',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( v4_relat_1 @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D )
        | ( sk_D
          = ( k7_relat_1 @ sk_D @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('64',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('65',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k2_partfun1 @ k1_xboole_0 @ X1 @ sk_D @ X0 )
        = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54','66'])).

thf('68',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('69',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('72',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
      | ( k1_xboole_0 = sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('74',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['41'])).

thf('76',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ k1_xboole_0 @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('78',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('79',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','79'])).

thf('81',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','48'])).

thf('82',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('83',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('89',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v4_relat_1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('92',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ( sk_D
        = ( k7_relat_1 @ sk_D @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['63','64'])).

thf('94',plain,
    ( ( sk_D
      = ( k7_relat_1 @ sk_D @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('96',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k1_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['94','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['63','64'])).

thf('100',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','100'])).

thf('102',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26
       != ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ~ ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
        | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 )
        | ~ ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','48'])).

thf('106',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('107',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('110',plain,(
    ! [X24: $i] :
      ( zip_tseitin_0 @ X24 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['108','110'])).

thf('112',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','112'])).

thf('114',plain,
    ( ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ( sk_A != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','113'])).

thf('115',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k2_partfun1 @ k1_xboole_0 @ X1 @ sk_D @ X0 )
        = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54','66'])).

thf('116',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('117',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['41'])).

thf('118',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('120',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('121',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('122',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['118','119','120','121'])).

thf('123',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['115','122'])).

thf('124',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','48'])).

thf('125',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['41'])).

thf('127',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('128',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['43','114','125','126','127'])).

thf('129',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['39','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','129'])).

thf('131',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('132',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('134',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k1_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['63','64'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','138'])).

thf('140',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X33 @ X34 @ X32 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('146',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('149',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('152',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['150','153'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('155',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X40 ) @ X41 )
      | ( v1_funct_2 @ X40 @ ( k1_relat_1 @ X40 ) @ X41 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('158',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('159',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['139','159'])).

thf('161',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','160'])).

thf('162',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','138'])).

thf('163',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['150','153'])).

thf('164',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X40 ) @ X41 )
      | ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X40 ) @ X41 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('167',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('168',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['162','168'])).

thf('170',plain,(
    $false ),
    inference(demod,[status(thm)],['161','169'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MmBEF2DdJZ
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:29:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 15.39/15.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 15.39/15.62  % Solved by: fo/fo7.sh
% 15.39/15.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.39/15.62  % done 7242 iterations in 15.163s
% 15.39/15.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 15.39/15.62  % SZS output start Refutation
% 15.39/15.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 15.39/15.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 15.39/15.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 15.39/15.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 15.39/15.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 15.39/15.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.39/15.62  thf(sk_C_type, type, sk_C: $i).
% 15.39/15.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 15.39/15.62  thf(sk_D_type, type, sk_D: $i).
% 15.39/15.62  thf(sk_B_type, type, sk_B: $i).
% 15.39/15.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 15.39/15.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.39/15.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 15.39/15.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 15.39/15.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 15.39/15.62  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 15.39/15.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 15.39/15.62  thf(sk_A_type, type, sk_A: $i).
% 15.39/15.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 15.39/15.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 15.39/15.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 15.39/15.62  thf(t38_funct_2, conjecture,
% 15.39/15.62    (![A:$i,B:$i,C:$i,D:$i]:
% 15.39/15.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 15.39/15.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.39/15.62       ( ( r1_tarski @ C @ A ) =>
% 15.39/15.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 15.39/15.62           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 15.39/15.62             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 15.39/15.62             ( m1_subset_1 @
% 15.39/15.62               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 15.39/15.62               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 15.39/15.62  thf(zf_stmt_0, negated_conjecture,
% 15.39/15.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 15.39/15.62        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 15.39/15.62            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.39/15.62          ( ( r1_tarski @ C @ A ) =>
% 15.39/15.62            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 15.39/15.62              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 15.39/15.62                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 15.39/15.62                ( m1_subset_1 @
% 15.39/15.62                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 15.39/15.62                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 15.39/15.62    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 15.39/15.62  thf('0', plain,
% 15.39/15.62      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 15.39/15.62        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 15.39/15.62             sk_B)
% 15.39/15.62        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 15.39/15.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf('1', plain,
% 15.39/15.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf(redefinition_k2_partfun1, axiom,
% 15.39/15.62    (![A:$i,B:$i,C:$i,D:$i]:
% 15.39/15.62     ( ( ( v1_funct_1 @ C ) & 
% 15.39/15.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.39/15.62       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 15.39/15.62  thf('2', plain,
% 15.39/15.62      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 15.39/15.62         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 15.39/15.62          | ~ (v1_funct_1 @ X36)
% 15.39/15.62          | ((k2_partfun1 @ X37 @ X38 @ X36 @ X39) = (k7_relat_1 @ X36 @ X39)))),
% 15.39/15.62      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 15.39/15.62  thf('3', plain,
% 15.39/15.62      (![X0 : $i]:
% 15.39/15.62         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 15.39/15.62          | ~ (v1_funct_1 @ sk_D))),
% 15.39/15.62      inference('sup-', [status(thm)], ['1', '2'])).
% 15.39/15.62  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf('5', plain,
% 15.39/15.62      (![X0 : $i]:
% 15.39/15.62         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 15.39/15.62      inference('demod', [status(thm)], ['3', '4'])).
% 15.39/15.62  thf('6', plain,
% 15.39/15.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf(dt_k2_partfun1, axiom,
% 15.39/15.62    (![A:$i,B:$i,C:$i,D:$i]:
% 15.39/15.62     ( ( ( v1_funct_1 @ C ) & 
% 15.39/15.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.39/15.62       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 15.39/15.62         ( m1_subset_1 @
% 15.39/15.62           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 15.39/15.62           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 15.39/15.62  thf('7', plain,
% 15.39/15.62      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 15.39/15.62         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 15.39/15.62          | ~ (v1_funct_1 @ X32)
% 15.39/15.62          | (v1_funct_1 @ (k2_partfun1 @ X33 @ X34 @ X32 @ X35)))),
% 15.39/15.62      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 15.39/15.62  thf('8', plain,
% 15.39/15.62      (![X0 : $i]:
% 15.39/15.62         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 15.39/15.62          | ~ (v1_funct_1 @ sk_D))),
% 15.39/15.62      inference('sup-', [status(thm)], ['6', '7'])).
% 15.39/15.62  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf('10', plain,
% 15.39/15.62      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 15.39/15.62      inference('demod', [status(thm)], ['8', '9'])).
% 15.39/15.62  thf('11', plain,
% 15.39/15.62      (![X0 : $i]:
% 15.39/15.62         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 15.39/15.62      inference('demod', [status(thm)], ['3', '4'])).
% 15.39/15.62  thf('12', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 15.39/15.62      inference('demod', [status(thm)], ['10', '11'])).
% 15.39/15.62  thf('13', plain,
% 15.39/15.62      (![X0 : $i]:
% 15.39/15.62         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 15.39/15.62      inference('demod', [status(thm)], ['3', '4'])).
% 15.39/15.62  thf('14', plain,
% 15.39/15.62      (![X0 : $i]:
% 15.39/15.62         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 15.39/15.62      inference('demod', [status(thm)], ['3', '4'])).
% 15.39/15.62  thf('15', plain,
% 15.39/15.62      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 15.39/15.62        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 15.39/15.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 15.39/15.62      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 15.39/15.62  thf('16', plain, ((r1_tarski @ sk_C @ sk_A)),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf(d1_funct_2, axiom,
% 15.39/15.62    (![A:$i,B:$i,C:$i]:
% 15.39/15.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.39/15.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.39/15.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 15.39/15.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 15.39/15.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.39/15.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 15.39/15.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 15.39/15.62  thf(zf_stmt_1, axiom,
% 15.39/15.62    (![B:$i,A:$i]:
% 15.39/15.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.39/15.62       ( zip_tseitin_0 @ B @ A ) ))).
% 15.39/15.62  thf('17', plain,
% 15.39/15.62      (![X24 : $i, X25 : $i]:
% 15.39/15.62         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.39/15.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 15.39/15.62  thf('18', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 15.39/15.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.39/15.62  thf('19', plain,
% 15.39/15.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.39/15.62         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 15.39/15.62      inference('sup+', [status(thm)], ['17', '18'])).
% 15.39/15.62  thf('20', plain,
% 15.39/15.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 15.39/15.62  thf(zf_stmt_3, axiom,
% 15.39/15.62    (![C:$i,B:$i,A:$i]:
% 15.39/15.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 15.39/15.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 15.39/15.62  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 15.39/15.62  thf(zf_stmt_5, axiom,
% 15.39/15.62    (![A:$i,B:$i,C:$i]:
% 15.39/15.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.39/15.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 15.39/15.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.39/15.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 15.39/15.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 15.39/15.62  thf('21', plain,
% 15.39/15.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 15.39/15.62         (~ (zip_tseitin_0 @ X29 @ X30)
% 15.39/15.62          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 15.39/15.62          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 15.39/15.62  thf('22', plain,
% 15.39/15.62      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 15.39/15.62      inference('sup-', [status(thm)], ['20', '21'])).
% 15.39/15.62  thf('23', plain,
% 15.39/15.62      (![X0 : $i]:
% 15.39/15.62         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 15.39/15.62      inference('sup-', [status(thm)], ['19', '22'])).
% 15.39/15.62  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf('25', plain,
% 15.39/15.62      (![X26 : $i, X27 : $i, X28 : $i]:
% 15.39/15.62         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 15.39/15.62          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 15.39/15.62          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 15.39/15.62  thf('26', plain,
% 15.39/15.62      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 15.39/15.62        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 15.39/15.62      inference('sup-', [status(thm)], ['24', '25'])).
% 15.39/15.62  thf('27', plain,
% 15.39/15.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf(redefinition_k1_relset_1, axiom,
% 15.39/15.62    (![A:$i,B:$i,C:$i]:
% 15.39/15.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.39/15.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 15.39/15.62  thf('28', plain,
% 15.39/15.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 15.39/15.62         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 15.39/15.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 15.39/15.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.39/15.62  thf('29', plain,
% 15.39/15.62      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 15.39/15.62      inference('sup-', [status(thm)], ['27', '28'])).
% 15.39/15.62  thf('30', plain,
% 15.39/15.62      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.39/15.62      inference('demod', [status(thm)], ['26', '29'])).
% 15.39/15.62  thf('31', plain,
% 15.39/15.62      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.39/15.62      inference('sup-', [status(thm)], ['23', '30'])).
% 15.39/15.62  thf('32', plain,
% 15.39/15.62      (![X24 : $i, X25 : $i]:
% 15.39/15.62         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.39/15.62  thf('33', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 15.39/15.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.39/15.62  thf(d10_xboole_0, axiom,
% 15.39/15.62    (![A:$i,B:$i]:
% 15.39/15.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 15.39/15.62  thf('34', plain,
% 15.39/15.62      (![X0 : $i, X2 : $i]:
% 15.39/15.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 15.39/15.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.39/15.62  thf('35', plain,
% 15.39/15.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 15.39/15.62      inference('sup-', [status(thm)], ['33', '34'])).
% 15.39/15.62  thf('36', plain,
% 15.39/15.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.39/15.62         (~ (r1_tarski @ X1 @ X0)
% 15.39/15.62          | (zip_tseitin_0 @ X0 @ X2)
% 15.39/15.62          | ((X1) = (k1_xboole_0)))),
% 15.39/15.62      inference('sup-', [status(thm)], ['32', '35'])).
% 15.39/15.62  thf('37', plain,
% 15.39/15.62      (![X0 : $i, X1 : $i]:
% 15.39/15.62         (((sk_A) = (k1_relat_1 @ sk_D))
% 15.39/15.62          | ((sk_B) = (k1_xboole_0))
% 15.39/15.62          | (zip_tseitin_0 @ X0 @ X1))),
% 15.39/15.62      inference('sup-', [status(thm)], ['31', '36'])).
% 15.39/15.62  thf('38', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf('39', plain,
% 15.39/15.62      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.39/15.62      inference('split', [status(esa)], ['38'])).
% 15.39/15.62  thf('40', plain,
% 15.39/15.62      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 15.39/15.62      inference('demod', [status(thm)], ['8', '9'])).
% 15.39/15.62  thf('41', plain,
% 15.39/15.62      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 15.39/15.62        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 15.39/15.62             sk_B)
% 15.39/15.62        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 15.39/15.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf('42', plain,
% 15.39/15.62      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))
% 15.39/15.62         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))))),
% 15.39/15.62      inference('split', [status(esa)], ['41'])).
% 15.39/15.62  thf('43', plain,
% 15.39/15.62      (((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 15.39/15.62      inference('sup-', [status(thm)], ['40', '42'])).
% 15.39/15.62  thf('44', plain,
% 15.39/15.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('split', [status(esa)], ['38'])).
% 15.39/15.62  thf('45', plain,
% 15.39/15.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf('46', plain,
% 15.39/15.62      (((m1_subset_1 @ sk_D @ 
% 15.39/15.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('sup+', [status(thm)], ['44', '45'])).
% 15.39/15.62  thf(t113_zfmisc_1, axiom,
% 15.39/15.62    (![A:$i,B:$i]:
% 15.39/15.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 15.39/15.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 15.39/15.62  thf('47', plain,
% 15.39/15.62      (![X5 : $i, X6 : $i]:
% 15.39/15.62         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 15.39/15.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 15.39/15.62  thf('48', plain,
% 15.39/15.62      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 15.39/15.62      inference('simplify', [status(thm)], ['47'])).
% 15.39/15.62  thf('49', plain,
% 15.39/15.62      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['46', '48'])).
% 15.39/15.62  thf('50', plain,
% 15.39/15.62      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 15.39/15.62      inference('simplify', [status(thm)], ['47'])).
% 15.39/15.62  thf('51', plain,
% 15.39/15.62      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 15.39/15.62         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 15.39/15.62          | ~ (v1_funct_1 @ X36)
% 15.39/15.62          | ((k2_partfun1 @ X37 @ X38 @ X36 @ X39) = (k7_relat_1 @ X36 @ X39)))),
% 15.39/15.62      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 15.39/15.62  thf('52', plain,
% 15.39/15.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.39/15.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 15.39/15.62          | ((k2_partfun1 @ k1_xboole_0 @ X0 @ X1 @ X2)
% 15.39/15.62              = (k7_relat_1 @ X1 @ X2))
% 15.39/15.62          | ~ (v1_funct_1 @ X1))),
% 15.39/15.62      inference('sup-', [status(thm)], ['50', '51'])).
% 15.39/15.62  thf('53', plain,
% 15.39/15.62      ((![X0 : $i, X1 : $i]:
% 15.39/15.62          (~ (v1_funct_1 @ sk_D)
% 15.39/15.62           | ((k2_partfun1 @ k1_xboole_0 @ X1 @ sk_D @ X0)
% 15.39/15.62               = (k7_relat_1 @ sk_D @ X0))))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('sup-', [status(thm)], ['49', '52'])).
% 15.39/15.62  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf('55', plain,
% 15.39/15.62      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['46', '48'])).
% 15.39/15.62  thf('56', plain,
% 15.39/15.62      (![X5 : $i, X6 : $i]:
% 15.39/15.62         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 15.39/15.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 15.39/15.62  thf('57', plain,
% 15.39/15.62      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 15.39/15.62      inference('simplify', [status(thm)], ['56'])).
% 15.39/15.62  thf(cc2_relset_1, axiom,
% 15.39/15.62    (![A:$i,B:$i,C:$i]:
% 15.39/15.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.39/15.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 15.39/15.62  thf('58', plain,
% 15.39/15.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 15.39/15.62         ((v4_relat_1 @ X18 @ X19)
% 15.39/15.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 15.39/15.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 15.39/15.62  thf('59', plain,
% 15.39/15.62      (![X0 : $i, X1 : $i]:
% 15.39/15.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 15.39/15.62          | (v4_relat_1 @ X1 @ X0))),
% 15.39/15.62      inference('sup-', [status(thm)], ['57', '58'])).
% 15.39/15.62  thf('60', plain,
% 15.39/15.62      ((![X0 : $i]: (v4_relat_1 @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('sup-', [status(thm)], ['55', '59'])).
% 15.39/15.62  thf(t209_relat_1, axiom,
% 15.39/15.62    (![A:$i,B:$i]:
% 15.39/15.62     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 15.39/15.62       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 15.39/15.62  thf('61', plain,
% 15.39/15.62      (![X11 : $i, X12 : $i]:
% 15.39/15.62         (((X11) = (k7_relat_1 @ X11 @ X12))
% 15.39/15.62          | ~ (v4_relat_1 @ X11 @ X12)
% 15.39/15.62          | ~ (v1_relat_1 @ X11))),
% 15.39/15.62      inference('cnf', [status(esa)], [t209_relat_1])).
% 15.39/15.62  thf('62', plain,
% 15.39/15.62      ((![X0 : $i]:
% 15.39/15.62          (~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ X0))))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('sup-', [status(thm)], ['60', '61'])).
% 15.39/15.62  thf('63', plain,
% 15.39/15.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf(cc1_relset_1, axiom,
% 15.39/15.62    (![A:$i,B:$i,C:$i]:
% 15.39/15.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.39/15.62       ( v1_relat_1 @ C ) ))).
% 15.39/15.62  thf('64', plain,
% 15.39/15.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 15.39/15.62         ((v1_relat_1 @ X15)
% 15.39/15.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 15.39/15.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.39/15.62  thf('65', plain, ((v1_relat_1 @ sk_D)),
% 15.39/15.62      inference('sup-', [status(thm)], ['63', '64'])).
% 15.39/15.62  thf('66', plain,
% 15.39/15.62      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['62', '65'])).
% 15.39/15.62  thf('67', plain,
% 15.39/15.62      ((![X0 : $i, X1 : $i]:
% 15.39/15.62          ((k2_partfun1 @ k1_xboole_0 @ X1 @ sk_D @ X0) = (sk_D)))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['53', '54', '66'])).
% 15.39/15.62  thf('68', plain,
% 15.39/15.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('split', [status(esa)], ['38'])).
% 15.39/15.62  thf('69', plain, ((r1_tarski @ sk_C @ sk_A)),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf('70', plain,
% 15.39/15.62      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('sup+', [status(thm)], ['68', '69'])).
% 15.39/15.62  thf('71', plain,
% 15.39/15.62      (![X0 : $i, X2 : $i]:
% 15.39/15.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 15.39/15.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.39/15.62  thf('72', plain,
% 15.39/15.62      (((~ (r1_tarski @ k1_xboole_0 @ sk_C) | ((k1_xboole_0) = (sk_C))))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('sup-', [status(thm)], ['70', '71'])).
% 15.39/15.62  thf('73', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 15.39/15.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.39/15.62  thf('74', plain,
% 15.39/15.62      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['72', '73'])).
% 15.39/15.62  thf('75', plain,
% 15.39/15.62      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))
% 15.39/15.62         <= (~
% 15.39/15.62             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 15.39/15.62               sk_B)))),
% 15.39/15.62      inference('split', [status(esa)], ['41'])).
% 15.39/15.62  thf('76', plain,
% 15.39/15.62      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 15.39/15.62           k1_xboole_0 @ sk_B))
% 15.39/15.62         <= (~
% 15.39/15.62             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 15.39/15.62               sk_B)) & 
% 15.39/15.62             (((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('sup-', [status(thm)], ['74', '75'])).
% 15.39/15.62  thf('77', plain,
% 15.39/15.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('split', [status(esa)], ['38'])).
% 15.39/15.62  thf('78', plain,
% 15.39/15.62      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['72', '73'])).
% 15.39/15.62  thf('79', plain,
% 15.39/15.62      ((~ (v1_funct_2 @ 
% 15.39/15.62           (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ k1_xboole_0) @ 
% 15.39/15.62           k1_xboole_0 @ sk_B))
% 15.39/15.62         <= (~
% 15.39/15.62             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 15.39/15.62               sk_B)) & 
% 15.39/15.62             (((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['76', '77', '78'])).
% 15.39/15.62  thf('80', plain,
% 15.39/15.62      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 15.39/15.62         <= (~
% 15.39/15.62             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 15.39/15.62               sk_B)) & 
% 15.39/15.62             (((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('sup-', [status(thm)], ['67', '79'])).
% 15.39/15.62  thf('81', plain,
% 15.39/15.62      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['46', '48'])).
% 15.39/15.62  thf('82', plain,
% 15.39/15.62      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 15.39/15.62      inference('simplify', [status(thm)], ['47'])).
% 15.39/15.62  thf('83', plain,
% 15.39/15.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 15.39/15.62         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 15.39/15.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 15.39/15.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.39/15.62  thf('84', plain,
% 15.39/15.62      (![X0 : $i, X1 : $i]:
% 15.39/15.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 15.39/15.62          | ((k1_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k1_relat_1 @ X1)))),
% 15.39/15.62      inference('sup-', [status(thm)], ['82', '83'])).
% 15.39/15.62  thf('85', plain,
% 15.39/15.62      ((![X0 : $i]:
% 15.39/15.62          ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_relat_1 @ sk_D)))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('sup-', [status(thm)], ['81', '84'])).
% 15.39/15.62  thf('86', plain,
% 15.39/15.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('split', [status(esa)], ['38'])).
% 15.39/15.62  thf('87', plain,
% 15.39/15.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf('88', plain,
% 15.39/15.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 15.39/15.62         ((v4_relat_1 @ X18 @ X19)
% 15.39/15.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 15.39/15.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 15.39/15.62  thf('89', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 15.39/15.62      inference('sup-', [status(thm)], ['87', '88'])).
% 15.39/15.62  thf('90', plain,
% 15.39/15.62      (((v4_relat_1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('sup+', [status(thm)], ['86', '89'])).
% 15.39/15.62  thf('91', plain,
% 15.39/15.62      (![X11 : $i, X12 : $i]:
% 15.39/15.62         (((X11) = (k7_relat_1 @ X11 @ X12))
% 15.39/15.62          | ~ (v4_relat_1 @ X11 @ X12)
% 15.39/15.62          | ~ (v1_relat_1 @ X11))),
% 15.39/15.62      inference('cnf', [status(esa)], [t209_relat_1])).
% 15.39/15.62  thf('92', plain,
% 15.39/15.62      (((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ k1_xboole_0))))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('sup-', [status(thm)], ['90', '91'])).
% 15.39/15.62  thf('93', plain, ((v1_relat_1 @ sk_D)),
% 15.39/15.62      inference('sup-', [status(thm)], ['63', '64'])).
% 15.39/15.62  thf('94', plain,
% 15.39/15.62      ((((sk_D) = (k7_relat_1 @ sk_D @ k1_xboole_0)))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['92', '93'])).
% 15.39/15.62  thf('95', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 15.39/15.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.39/15.62  thf(t91_relat_1, axiom,
% 15.39/15.62    (![A:$i,B:$i]:
% 15.39/15.62     ( ( v1_relat_1 @ B ) =>
% 15.39/15.62       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 15.39/15.62         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 15.39/15.62  thf('96', plain,
% 15.39/15.62      (![X13 : $i, X14 : $i]:
% 15.39/15.62         (~ (r1_tarski @ X13 @ (k1_relat_1 @ X14))
% 15.39/15.62          | ((k1_relat_1 @ (k7_relat_1 @ X14 @ X13)) = (X13))
% 15.39/15.62          | ~ (v1_relat_1 @ X14))),
% 15.39/15.62      inference('cnf', [status(esa)], [t91_relat_1])).
% 15.39/15.62  thf('97', plain,
% 15.39/15.62      (![X0 : $i]:
% 15.39/15.62         (~ (v1_relat_1 @ X0)
% 15.39/15.62          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 15.39/15.62      inference('sup-', [status(thm)], ['95', '96'])).
% 15.39/15.62  thf('98', plain,
% 15.39/15.62      (((((k1_relat_1 @ sk_D) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_D)))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('sup+', [status(thm)], ['94', '97'])).
% 15.39/15.62  thf('99', plain, ((v1_relat_1 @ sk_D)),
% 15.39/15.62      inference('sup-', [status(thm)], ['63', '64'])).
% 15.39/15.62  thf('100', plain,
% 15.39/15.62      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['98', '99'])).
% 15.39/15.62  thf('101', plain,
% 15.39/15.62      ((![X0 : $i]: ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_xboole_0)))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['85', '100'])).
% 15.39/15.62  thf('102', plain,
% 15.39/15.62      (![X26 : $i, X27 : $i, X28 : $i]:
% 15.39/15.62         (((X26) != (k1_relset_1 @ X26 @ X27 @ X28))
% 15.39/15.62          | (v1_funct_2 @ X28 @ X26 @ X27)
% 15.39/15.62          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 15.39/15.62  thf('103', plain,
% 15.39/15.62      ((![X0 : $i]:
% 15.39/15.62          (((k1_xboole_0) != (k1_xboole_0))
% 15.39/15.62           | ~ (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0)
% 15.39/15.62           | (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0)))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('sup-', [status(thm)], ['101', '102'])).
% 15.39/15.62  thf('104', plain,
% 15.39/15.62      ((![X0 : $i]:
% 15.39/15.62          ((v1_funct_2 @ sk_D @ k1_xboole_0 @ X0)
% 15.39/15.62           | ~ (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0)))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('simplify', [status(thm)], ['103'])).
% 15.39/15.62  thf('105', plain,
% 15.39/15.62      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['46', '48'])).
% 15.39/15.62  thf('106', plain,
% 15.39/15.62      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 15.39/15.62      inference('simplify', [status(thm)], ['47'])).
% 15.39/15.62  thf('107', plain,
% 15.39/15.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 15.39/15.62         (~ (zip_tseitin_0 @ X29 @ X30)
% 15.39/15.62          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 15.39/15.62          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 15.39/15.62  thf('108', plain,
% 15.39/15.62      (![X0 : $i, X1 : $i]:
% 15.39/15.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 15.39/15.62          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 15.39/15.62          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 15.39/15.62      inference('sup-', [status(thm)], ['106', '107'])).
% 15.39/15.62  thf('109', plain,
% 15.39/15.62      (![X24 : $i, X25 : $i]:
% 15.39/15.62         ((zip_tseitin_0 @ X24 @ X25) | ((X25) != (k1_xboole_0)))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.39/15.62  thf('110', plain, (![X24 : $i]: (zip_tseitin_0 @ X24 @ k1_xboole_0)),
% 15.39/15.62      inference('simplify', [status(thm)], ['109'])).
% 15.39/15.62  thf('111', plain,
% 15.39/15.62      (![X0 : $i, X1 : $i]:
% 15.39/15.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 15.39/15.62          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 15.39/15.62      inference('demod', [status(thm)], ['108', '110'])).
% 15.39/15.62  thf('112', plain,
% 15.39/15.62      ((![X0 : $i]: (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('sup-', [status(thm)], ['105', '111'])).
% 15.39/15.62  thf('113', plain,
% 15.39/15.62      ((![X0 : $i]: (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['104', '112'])).
% 15.39/15.62  thf('114', plain,
% 15.39/15.62      (((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)) | 
% 15.39/15.62       ~ (((sk_A) = (k1_xboole_0)))),
% 15.39/15.62      inference('demod', [status(thm)], ['80', '113'])).
% 15.39/15.62  thf('115', plain,
% 15.39/15.62      ((![X0 : $i, X1 : $i]:
% 15.39/15.62          ((k2_partfun1 @ k1_xboole_0 @ X1 @ sk_D @ X0) = (sk_D)))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['53', '54', '66'])).
% 15.39/15.62  thf('116', plain,
% 15.39/15.62      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['72', '73'])).
% 15.39/15.62  thf('117', plain,
% 15.39/15.62      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 15.39/15.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 15.39/15.62         <= (~
% 15.39/15.62             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 15.39/15.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 15.39/15.62      inference('split', [status(esa)], ['41'])).
% 15.39/15.62  thf('118', plain,
% 15.39/15.62      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 15.39/15.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 15.39/15.62         <= (~
% 15.39/15.62             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 15.39/15.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) & 
% 15.39/15.62             (((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('sup-', [status(thm)], ['116', '117'])).
% 15.39/15.62  thf('119', plain,
% 15.39/15.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('split', [status(esa)], ['38'])).
% 15.39/15.62  thf('120', plain,
% 15.39/15.62      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['72', '73'])).
% 15.39/15.62  thf('121', plain,
% 15.39/15.62      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 15.39/15.62      inference('simplify', [status(thm)], ['47'])).
% 15.39/15.62  thf('122', plain,
% 15.39/15.62      ((~ (m1_subset_1 @ 
% 15.39/15.62           (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ k1_xboole_0) @ 
% 15.39/15.62           (k1_zfmisc_1 @ k1_xboole_0)))
% 15.39/15.62         <= (~
% 15.39/15.62             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 15.39/15.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) & 
% 15.39/15.62             (((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['118', '119', '120', '121'])).
% 15.39/15.62  thf('123', plain,
% 15.39/15.62      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 15.39/15.62         <= (~
% 15.39/15.62             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 15.39/15.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) & 
% 15.39/15.62             (((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('sup-', [status(thm)], ['115', '122'])).
% 15.39/15.62  thf('124', plain,
% 15.39/15.62      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 15.39/15.62         <= ((((sk_A) = (k1_xboole_0))))),
% 15.39/15.62      inference('demod', [status(thm)], ['46', '48'])).
% 15.39/15.62  thf('125', plain,
% 15.39/15.62      (~ (((sk_A) = (k1_xboole_0))) | 
% 15.39/15.62       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 15.39/15.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 15.39/15.62      inference('demod', [status(thm)], ['123', '124'])).
% 15.39/15.62  thf('126', plain,
% 15.39/15.62      (~
% 15.39/15.62       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 15.39/15.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) | 
% 15.39/15.62       ~
% 15.39/15.62       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)) | 
% 15.39/15.62       ~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 15.39/15.62      inference('split', [status(esa)], ['41'])).
% 15.39/15.62  thf('127', plain,
% 15.39/15.62      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 15.39/15.62      inference('split', [status(esa)], ['38'])).
% 15.39/15.62  thf('128', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 15.39/15.62      inference('sat_resolution*', [status(thm)],
% 15.39/15.62                ['43', '114', '125', '126', '127'])).
% 15.39/15.62  thf('129', plain, (((sk_B) != (k1_xboole_0))),
% 15.39/15.62      inference('simpl_trail', [status(thm)], ['39', '128'])).
% 15.39/15.62  thf('130', plain,
% 15.39/15.62      (![X0 : $i, X1 : $i]:
% 15.39/15.62         (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ X0 @ X1))),
% 15.39/15.62      inference('simplify_reflect-', [status(thm)], ['37', '129'])).
% 15.39/15.62  thf('131', plain,
% 15.39/15.62      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 15.39/15.62      inference('sup-', [status(thm)], ['20', '21'])).
% 15.39/15.62  thf('132', plain,
% 15.39/15.62      ((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 15.39/15.62      inference('sup-', [status(thm)], ['130', '131'])).
% 15.39/15.62  thf('133', plain,
% 15.39/15.62      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.39/15.62      inference('demod', [status(thm)], ['26', '29'])).
% 15.39/15.62  thf('134', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 15.39/15.62      inference('clc', [status(thm)], ['132', '133'])).
% 15.39/15.62  thf('135', plain,
% 15.39/15.62      (![X13 : $i, X14 : $i]:
% 15.39/15.62         (~ (r1_tarski @ X13 @ (k1_relat_1 @ X14))
% 15.39/15.62          | ((k1_relat_1 @ (k7_relat_1 @ X14 @ X13)) = (X13))
% 15.39/15.62          | ~ (v1_relat_1 @ X14))),
% 15.39/15.62      inference('cnf', [status(esa)], [t91_relat_1])).
% 15.39/15.62  thf('136', plain,
% 15.39/15.62      (![X0 : $i]:
% 15.39/15.62         (~ (r1_tarski @ X0 @ sk_A)
% 15.39/15.62          | ~ (v1_relat_1 @ sk_D)
% 15.39/15.62          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 15.39/15.62      inference('sup-', [status(thm)], ['134', '135'])).
% 15.39/15.62  thf('137', plain, ((v1_relat_1 @ sk_D)),
% 15.39/15.62      inference('sup-', [status(thm)], ['63', '64'])).
% 15.39/15.62  thf('138', plain,
% 15.39/15.62      (![X0 : $i]:
% 15.39/15.62         (~ (r1_tarski @ X0 @ sk_A)
% 15.39/15.62          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 15.39/15.62      inference('demod', [status(thm)], ['136', '137'])).
% 15.39/15.62  thf('139', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 15.39/15.62      inference('sup-', [status(thm)], ['16', '138'])).
% 15.39/15.62  thf('140', plain,
% 15.39/15.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf('141', plain,
% 15.39/15.62      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 15.39/15.62         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 15.39/15.62          | ~ (v1_funct_1 @ X32)
% 15.39/15.62          | (m1_subset_1 @ (k2_partfun1 @ X33 @ X34 @ X32 @ X35) @ 
% 15.39/15.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 15.39/15.62      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 15.39/15.62  thf('142', plain,
% 15.39/15.62      (![X0 : $i]:
% 15.39/15.62         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 15.39/15.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 15.39/15.62          | ~ (v1_funct_1 @ sk_D))),
% 15.39/15.62      inference('sup-', [status(thm)], ['140', '141'])).
% 15.39/15.62  thf('143', plain, ((v1_funct_1 @ sk_D)),
% 15.39/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.39/15.62  thf('144', plain,
% 15.39/15.62      (![X0 : $i]:
% 15.39/15.62         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 15.39/15.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.39/15.62      inference('demod', [status(thm)], ['142', '143'])).
% 15.39/15.62  thf('145', plain,
% 15.39/15.62      (![X0 : $i]:
% 15.39/15.62         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 15.39/15.62      inference('demod', [status(thm)], ['3', '4'])).
% 15.39/15.62  thf('146', plain,
% 15.39/15.62      (![X0 : $i]:
% 15.39/15.62         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.39/15.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.39/15.62      inference('demod', [status(thm)], ['144', '145'])).
% 15.39/15.62  thf('147', plain,
% 15.39/15.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 15.39/15.63         ((v5_relat_1 @ X18 @ X20)
% 15.39/15.63          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 15.39/15.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 15.39/15.63  thf('148', plain,
% 15.39/15.63      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 15.39/15.63      inference('sup-', [status(thm)], ['146', '147'])).
% 15.39/15.63  thf(d19_relat_1, axiom,
% 15.39/15.63    (![A:$i,B:$i]:
% 15.39/15.63     ( ( v1_relat_1 @ B ) =>
% 15.39/15.63       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 15.39/15.63  thf('149', plain,
% 15.39/15.63      (![X7 : $i, X8 : $i]:
% 15.39/15.63         (~ (v5_relat_1 @ X7 @ X8)
% 15.39/15.63          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 15.39/15.63          | ~ (v1_relat_1 @ X7))),
% 15.39/15.63      inference('cnf', [status(esa)], [d19_relat_1])).
% 15.39/15.63  thf('150', plain,
% 15.39/15.63      (![X0 : $i]:
% 15.39/15.63         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 15.39/15.63          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 15.39/15.63      inference('sup-', [status(thm)], ['148', '149'])).
% 15.39/15.63  thf('151', plain,
% 15.39/15.63      (![X0 : $i]:
% 15.39/15.63         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.39/15.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.39/15.63      inference('demod', [status(thm)], ['144', '145'])).
% 15.39/15.63  thf('152', plain,
% 15.39/15.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 15.39/15.63         ((v1_relat_1 @ X15)
% 15.39/15.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 15.39/15.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.39/15.63  thf('153', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 15.39/15.63      inference('sup-', [status(thm)], ['151', '152'])).
% 15.39/15.63  thf('154', plain,
% 15.39/15.63      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 15.39/15.63      inference('demod', [status(thm)], ['150', '153'])).
% 15.39/15.63  thf(t4_funct_2, axiom,
% 15.39/15.63    (![A:$i,B:$i]:
% 15.39/15.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 15.39/15.63       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 15.39/15.63         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 15.39/15.63           ( m1_subset_1 @
% 15.39/15.63             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 15.39/15.63  thf('155', plain,
% 15.39/15.63      (![X40 : $i, X41 : $i]:
% 15.39/15.63         (~ (r1_tarski @ (k2_relat_1 @ X40) @ X41)
% 15.39/15.63          | (v1_funct_2 @ X40 @ (k1_relat_1 @ X40) @ X41)
% 15.39/15.63          | ~ (v1_funct_1 @ X40)
% 15.39/15.63          | ~ (v1_relat_1 @ X40))),
% 15.39/15.63      inference('cnf', [status(esa)], [t4_funct_2])).
% 15.39/15.63  thf('156', plain,
% 15.39/15.63      (![X0 : $i]:
% 15.39/15.63         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 15.39/15.63          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 15.39/15.63          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.39/15.63             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 15.39/15.63      inference('sup-', [status(thm)], ['154', '155'])).
% 15.39/15.63  thf('157', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 15.39/15.63      inference('sup-', [status(thm)], ['151', '152'])).
% 15.39/15.63  thf('158', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 15.39/15.63      inference('demod', [status(thm)], ['10', '11'])).
% 15.39/15.63  thf('159', plain,
% 15.39/15.63      (![X0 : $i]:
% 15.39/15.63         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.39/15.63          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 15.39/15.63      inference('demod', [status(thm)], ['156', '157', '158'])).
% 15.39/15.63  thf('160', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 15.39/15.63      inference('sup+', [status(thm)], ['139', '159'])).
% 15.39/15.63  thf('161', plain,
% 15.39/15.63      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 15.39/15.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 15.39/15.63      inference('demod', [status(thm)], ['15', '160'])).
% 15.39/15.63  thf('162', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 15.39/15.63      inference('sup-', [status(thm)], ['16', '138'])).
% 15.39/15.63  thf('163', plain,
% 15.39/15.63      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 15.39/15.63      inference('demod', [status(thm)], ['150', '153'])).
% 15.39/15.63  thf('164', plain,
% 15.39/15.63      (![X40 : $i, X41 : $i]:
% 15.39/15.63         (~ (r1_tarski @ (k2_relat_1 @ X40) @ X41)
% 15.39/15.63          | (m1_subset_1 @ X40 @ 
% 15.39/15.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X40) @ X41)))
% 15.39/15.63          | ~ (v1_funct_1 @ X40)
% 15.39/15.63          | ~ (v1_relat_1 @ X40))),
% 15.39/15.63      inference('cnf', [status(esa)], [t4_funct_2])).
% 15.39/15.63  thf('165', plain,
% 15.39/15.63      (![X0 : $i]:
% 15.39/15.63         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 15.39/15.63          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 15.39/15.63          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.39/15.63             (k1_zfmisc_1 @ 
% 15.39/15.63              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 15.39/15.63      inference('sup-', [status(thm)], ['163', '164'])).
% 15.39/15.63  thf('166', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 15.39/15.63      inference('sup-', [status(thm)], ['151', '152'])).
% 15.39/15.63  thf('167', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 15.39/15.63      inference('demod', [status(thm)], ['10', '11'])).
% 15.39/15.63  thf('168', plain,
% 15.39/15.63      (![X0 : $i]:
% 15.39/15.63         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.39/15.63          (k1_zfmisc_1 @ 
% 15.39/15.63           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 15.39/15.63      inference('demod', [status(thm)], ['165', '166', '167'])).
% 15.39/15.63  thf('169', plain,
% 15.39/15.63      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 15.39/15.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 15.39/15.63      inference('sup+', [status(thm)], ['162', '168'])).
% 15.39/15.63  thf('170', plain, ($false), inference('demod', [status(thm)], ['161', '169'])).
% 15.39/15.63  
% 15.39/15.63  % SZS output end Refutation
% 15.39/15.63  
% 15.46/15.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
