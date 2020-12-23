%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VnxbI4qHGZ

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:43 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  187 (3007 expanded)
%              Number of leaves         :   41 ( 826 expanded)
%              Depth                    :   30
%              Number of atoms          : 1501 (53077 expanded)
%              Number of equality atoms :  131 (3895 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k2_partfun1 @ X44 @ X45 @ X43 @ X46 )
        = ( k7_relat_1 @ X43 @ X46 ) ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X40 @ X41 @ X39 @ X42 ) ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('29',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('32',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('36',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('40',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

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
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('51',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( v4_relat_1 @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D )
        | ( sk_D
          = ( k7_relat_1 @ sk_D @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('58',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('60',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('61',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('63',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5','12','13','14'])).

thf('64',plain,
    ( ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('66',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('68',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('69',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('71',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','48'])).

thf('72',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('74',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','48'])).

thf('76',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('77',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('81',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('84',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('86',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','48'])).

thf('88',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('89',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('92',plain,(
    ! [X31: $i] :
      ( zip_tseitin_0 @ X31 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['90','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','93'])).

thf('95',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','94'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','95'])).

thf('97',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ~ ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
        | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','93'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['64','69','70','71','72','73','74','101'])).

thf('103',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('104',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['102','103'])).

thf('105',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['43','104'])).

thf('106',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['41','105'])).

thf('107',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','106'])).

thf('108',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['43','104'])).

thf('109',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['107','108'])).

thf('110',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['25','109'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('111',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['59','60'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['18','114'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('116',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('117',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ( ( r1_tarski @ A @ D )
       => ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('118',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( r1_tarski @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_relset_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['59','60'])).

thf('122',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['115','124'])).

thf('126',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','125'])).

thf('127',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['15','126'])).

thf('128',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','125'])).

thf('129',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('130',plain,
    ( ( k1_relset_1 @ sk_C @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['18','114'])).

thf('132',plain,
    ( ( k1_relset_1 @ sk_C @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('134',plain,
    ( ( sk_C != sk_C )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('137',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','125'])).

thf('138',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('139',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['136','139'])).

thf('141',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['43','104'])).

thf('142',plain,(
    zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['135','142'])).

thf('144',plain,(
    $false ),
    inference(demod,[status(thm)],['127','143'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VnxbI4qHGZ
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:05:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 2.10/2.36  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.10/2.36  % Solved by: fo/fo7.sh
% 2.10/2.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.10/2.36  % done 1696 iterations in 1.892s
% 2.10/2.36  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.10/2.36  % SZS output start Refutation
% 2.10/2.36  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.10/2.36  thf(sk_C_type, type, sk_C: $i).
% 2.10/2.36  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.10/2.36  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.10/2.36  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.10/2.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.10/2.36  thf(sk_D_type, type, sk_D: $i).
% 2.10/2.36  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 2.10/2.36  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.10/2.36  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.10/2.36  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.10/2.36  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.10/2.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.10/2.36  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.10/2.36  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.10/2.36  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.10/2.36  thf(sk_A_type, type, sk_A: $i).
% 2.10/2.36  thf(sk_B_type, type, sk_B: $i).
% 2.10/2.36  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.10/2.36  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.10/2.36  thf(t38_funct_2, conjecture,
% 2.10/2.36    (![A:$i,B:$i,C:$i,D:$i]:
% 2.10/2.36     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.10/2.36         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.10/2.36       ( ( r1_tarski @ C @ A ) =>
% 2.10/2.36         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 2.10/2.36           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 2.10/2.36             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 2.10/2.36             ( m1_subset_1 @
% 2.10/2.36               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 2.10/2.36               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 2.10/2.36  thf(zf_stmt_0, negated_conjecture,
% 2.10/2.36    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.10/2.36        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.10/2.36            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.10/2.36          ( ( r1_tarski @ C @ A ) =>
% 2.10/2.36            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 2.10/2.36              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 2.10/2.36                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 2.10/2.36                ( m1_subset_1 @
% 2.10/2.36                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 2.10/2.36                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 2.10/2.36    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 2.10/2.36  thf('0', plain,
% 2.10/2.36      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 2.10/2.36        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 2.10/2.36             sk_B)
% 2.10/2.36        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 2.10/2.36             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.36  thf('1', plain,
% 2.10/2.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.36  thf(redefinition_k2_partfun1, axiom,
% 2.10/2.36    (![A:$i,B:$i,C:$i,D:$i]:
% 2.10/2.36     ( ( ( v1_funct_1 @ C ) & 
% 2.10/2.36         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.10/2.36       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 2.10/2.36  thf('2', plain,
% 2.10/2.36      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 2.10/2.36         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.10/2.36          | ~ (v1_funct_1 @ X43)
% 2.10/2.36          | ((k2_partfun1 @ X44 @ X45 @ X43 @ X46) = (k7_relat_1 @ X43 @ X46)))),
% 2.10/2.36      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 2.10/2.36  thf('3', plain,
% 2.10/2.36      (![X0 : $i]:
% 2.10/2.36         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 2.10/2.36          | ~ (v1_funct_1 @ sk_D))),
% 2.10/2.36      inference('sup-', [status(thm)], ['1', '2'])).
% 2.10/2.36  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.36  thf('5', plain,
% 2.10/2.36      (![X0 : $i]:
% 2.10/2.36         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 2.10/2.36      inference('demod', [status(thm)], ['3', '4'])).
% 2.10/2.36  thf('6', plain,
% 2.10/2.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.36  thf(dt_k2_partfun1, axiom,
% 2.10/2.36    (![A:$i,B:$i,C:$i,D:$i]:
% 2.10/2.36     ( ( ( v1_funct_1 @ C ) & 
% 2.10/2.36         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.10/2.36       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 2.10/2.36         ( m1_subset_1 @
% 2.10/2.36           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 2.10/2.36           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 2.10/2.36  thf('7', plain,
% 2.10/2.36      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 2.10/2.36         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 2.10/2.36          | ~ (v1_funct_1 @ X39)
% 2.10/2.36          | (v1_funct_1 @ (k2_partfun1 @ X40 @ X41 @ X39 @ X42)))),
% 2.10/2.36      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 2.10/2.36  thf('8', plain,
% 2.10/2.36      (![X0 : $i]:
% 2.10/2.36         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 2.10/2.36          | ~ (v1_funct_1 @ sk_D))),
% 2.10/2.36      inference('sup-', [status(thm)], ['6', '7'])).
% 2.10/2.36  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.36  thf('10', plain,
% 2.10/2.36      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 2.10/2.36      inference('demod', [status(thm)], ['8', '9'])).
% 2.10/2.36  thf('11', plain,
% 2.10/2.36      (![X0 : $i]:
% 2.10/2.36         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 2.10/2.36      inference('demod', [status(thm)], ['3', '4'])).
% 2.10/2.36  thf('12', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 2.10/2.36      inference('demod', [status(thm)], ['10', '11'])).
% 2.10/2.36  thf('13', plain,
% 2.10/2.36      (![X0 : $i]:
% 2.10/2.36         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 2.10/2.36      inference('demod', [status(thm)], ['3', '4'])).
% 2.10/2.36  thf('14', plain,
% 2.10/2.36      (![X0 : $i]:
% 2.10/2.36         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 2.10/2.36      inference('demod', [status(thm)], ['3', '4'])).
% 2.10/2.36  thf('15', plain,
% 2.10/2.36      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 2.10/2.36        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 2.10/2.36             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 2.10/2.36      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 2.10/2.36  thf(d10_xboole_0, axiom,
% 2.10/2.36    (![A:$i,B:$i]:
% 2.10/2.36     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.10/2.36  thf('16', plain,
% 2.10/2.36      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.10/2.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.10/2.36  thf('17', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.10/2.36      inference('simplify', [status(thm)], ['16'])).
% 2.10/2.36  thf('18', plain, ((r1_tarski @ sk_C @ sk_A)),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.36  thf('19', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.36  thf(d1_funct_2, axiom,
% 2.10/2.36    (![A:$i,B:$i,C:$i]:
% 2.10/2.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.10/2.36       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.10/2.36           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.10/2.36             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.10/2.36         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.10/2.36           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.10/2.36             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.10/2.36  thf(zf_stmt_1, axiom,
% 2.10/2.36    (![C:$i,B:$i,A:$i]:
% 2.10/2.36     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.10/2.36       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.10/2.36  thf('20', plain,
% 2.10/2.36      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.10/2.36         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 2.10/2.36          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 2.10/2.36          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.10/2.36  thf('21', plain,
% 2.10/2.36      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 2.10/2.36        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 2.10/2.36      inference('sup-', [status(thm)], ['19', '20'])).
% 2.10/2.36  thf('22', plain,
% 2.10/2.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.36  thf(redefinition_k1_relset_1, axiom,
% 2.10/2.36    (![A:$i,B:$i,C:$i]:
% 2.10/2.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.10/2.36       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.10/2.36  thf('23', plain,
% 2.10/2.36      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.10/2.36         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 2.10/2.36          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.10/2.36      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.10/2.36  thf('24', plain,
% 2.10/2.36      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.10/2.36      inference('sup-', [status(thm)], ['22', '23'])).
% 2.10/2.36  thf('25', plain,
% 2.10/2.36      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.10/2.36      inference('demod', [status(thm)], ['21', '24'])).
% 2.10/2.36  thf(zf_stmt_2, axiom,
% 2.10/2.36    (![B:$i,A:$i]:
% 2.10/2.36     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.10/2.36       ( zip_tseitin_0 @ B @ A ) ))).
% 2.10/2.36  thf('26', plain,
% 2.10/2.36      (![X31 : $i, X32 : $i]:
% 2.10/2.36         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.10/2.36  thf('27', plain,
% 2.10/2.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.36  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.10/2.36  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.10/2.36  thf(zf_stmt_5, axiom,
% 2.10/2.36    (![A:$i,B:$i,C:$i]:
% 2.10/2.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.10/2.36       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.10/2.36         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.10/2.36           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.10/2.36             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.10/2.36  thf('28', plain,
% 2.10/2.36      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.10/2.36         (~ (zip_tseitin_0 @ X36 @ X37)
% 2.10/2.36          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 2.10/2.36          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.10/2.36  thf('29', plain,
% 2.10/2.36      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.10/2.36      inference('sup-', [status(thm)], ['27', '28'])).
% 2.10/2.36  thf('30', plain,
% 2.10/2.36      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 2.10/2.36      inference('sup-', [status(thm)], ['26', '29'])).
% 2.10/2.36  thf('31', plain,
% 2.10/2.36      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.10/2.36      inference('demod', [status(thm)], ['21', '24'])).
% 2.10/2.36  thf('32', plain,
% 2.10/2.36      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.10/2.36      inference('sup-', [status(thm)], ['30', '31'])).
% 2.10/2.36  thf('33', plain,
% 2.10/2.36      (![X31 : $i, X32 : $i]:
% 2.10/2.36         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.10/2.36  thf('34', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.10/2.36      inference('simplify', [status(thm)], ['16'])).
% 2.10/2.36  thf('35', plain,
% 2.10/2.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.36  thf(t13_relset_1, axiom,
% 2.10/2.36    (![A:$i,B:$i,C:$i,D:$i]:
% 2.10/2.36     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 2.10/2.36       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 2.10/2.36         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 2.10/2.36  thf('36', plain,
% 2.10/2.36      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 2.10/2.36         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 2.10/2.36          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 2.10/2.36          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 2.10/2.36      inference('cnf', [status(esa)], [t13_relset_1])).
% 2.10/2.36  thf('37', plain,
% 2.10/2.36      (![X0 : $i]:
% 2.10/2.36         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 2.10/2.36          | ~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 2.10/2.36      inference('sup-', [status(thm)], ['35', '36'])).
% 2.10/2.36  thf('38', plain,
% 2.10/2.36      ((m1_subset_1 @ sk_D @ 
% 2.10/2.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 2.10/2.36      inference('sup-', [status(thm)], ['34', '37'])).
% 2.10/2.36  thf('39', plain,
% 2.10/2.36      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.10/2.36         (~ (zip_tseitin_0 @ X36 @ X37)
% 2.10/2.36          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 2.10/2.36          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.10/2.36  thf('40', plain,
% 2.10/2.36      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D))
% 2.10/2.36        | ~ (zip_tseitin_0 @ sk_B @ (k1_relat_1 @ sk_D)))),
% 2.10/2.36      inference('sup-', [status(thm)], ['38', '39'])).
% 2.10/2.36  thf('41', plain,
% 2.10/2.36      ((((sk_B) = (k1_xboole_0))
% 2.10/2.36        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D)))),
% 2.10/2.36      inference('sup-', [status(thm)], ['33', '40'])).
% 2.10/2.36  thf('42', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.36  thf('43', plain,
% 2.10/2.36      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.10/2.36      inference('split', [status(esa)], ['42'])).
% 2.10/2.36  thf('44', plain,
% 2.10/2.36      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('split', [status(esa)], ['42'])).
% 2.10/2.36  thf('45', plain,
% 2.10/2.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.36  thf('46', plain,
% 2.10/2.36      (((m1_subset_1 @ sk_D @ 
% 2.10/2.36         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('sup+', [status(thm)], ['44', '45'])).
% 2.10/2.36  thf(t113_zfmisc_1, axiom,
% 2.10/2.36    (![A:$i,B:$i]:
% 2.10/2.36     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.10/2.36       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.10/2.36  thf('47', plain,
% 2.10/2.36      (![X5 : $i, X6 : $i]:
% 2.10/2.36         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 2.10/2.36      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.10/2.36  thf('48', plain,
% 2.10/2.36      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 2.10/2.36      inference('simplify', [status(thm)], ['47'])).
% 2.10/2.36  thf('49', plain,
% 2.10/2.36      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('demod', [status(thm)], ['46', '48'])).
% 2.10/2.36  thf('50', plain,
% 2.10/2.36      (![X5 : $i, X6 : $i]:
% 2.10/2.36         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 2.10/2.36      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.10/2.36  thf('51', plain,
% 2.10/2.36      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 2.10/2.36      inference('simplify', [status(thm)], ['50'])).
% 2.10/2.36  thf(cc2_relset_1, axiom,
% 2.10/2.36    (![A:$i,B:$i,C:$i]:
% 2.10/2.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.10/2.36       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.10/2.36  thf('52', plain,
% 2.10/2.36      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.10/2.36         ((v4_relat_1 @ X17 @ X18)
% 2.10/2.36          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 2.10/2.36      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.10/2.36  thf('53', plain,
% 2.10/2.36      (![X0 : $i, X1 : $i]:
% 2.10/2.36         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.10/2.36          | (v4_relat_1 @ X1 @ X0))),
% 2.10/2.36      inference('sup-', [status(thm)], ['51', '52'])).
% 2.10/2.36  thf('54', plain,
% 2.10/2.36      ((![X0 : $i]: (v4_relat_1 @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('sup-', [status(thm)], ['49', '53'])).
% 2.10/2.36  thf(t209_relat_1, axiom,
% 2.10/2.36    (![A:$i,B:$i]:
% 2.10/2.36     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.10/2.36       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 2.10/2.36  thf('55', plain,
% 2.10/2.36      (![X11 : $i, X12 : $i]:
% 2.10/2.36         (((X11) = (k7_relat_1 @ X11 @ X12))
% 2.10/2.36          | ~ (v4_relat_1 @ X11 @ X12)
% 2.10/2.36          | ~ (v1_relat_1 @ X11))),
% 2.10/2.36      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.10/2.36  thf('56', plain,
% 2.10/2.36      ((![X0 : $i]:
% 2.10/2.36          (~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ X0))))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('sup-', [status(thm)], ['54', '55'])).
% 2.10/2.36  thf('57', plain,
% 2.10/2.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.36  thf(cc2_relat_1, axiom,
% 2.10/2.36    (![A:$i]:
% 2.10/2.36     ( ( v1_relat_1 @ A ) =>
% 2.10/2.36       ( ![B:$i]:
% 2.10/2.36         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.10/2.36  thf('58', plain,
% 2.10/2.36      (![X7 : $i, X8 : $i]:
% 2.10/2.36         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 2.10/2.36          | (v1_relat_1 @ X7)
% 2.10/2.36          | ~ (v1_relat_1 @ X8))),
% 2.10/2.36      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.10/2.36  thf('59', plain,
% 2.10/2.36      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 2.10/2.36      inference('sup-', [status(thm)], ['57', '58'])).
% 2.10/2.36  thf(fc6_relat_1, axiom,
% 2.10/2.36    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.10/2.36  thf('60', plain,
% 2.10/2.36      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 2.10/2.36      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.10/2.36  thf('61', plain, ((v1_relat_1 @ sk_D)),
% 2.10/2.36      inference('demod', [status(thm)], ['59', '60'])).
% 2.10/2.36  thf('62', plain,
% 2.10/2.36      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('demod', [status(thm)], ['56', '61'])).
% 2.10/2.36  thf('63', plain,
% 2.10/2.36      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 2.10/2.36        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 2.10/2.36             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 2.10/2.36      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 2.10/2.36  thf('64', plain,
% 2.10/2.36      (((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 2.10/2.36         | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('sup-', [status(thm)], ['62', '63'])).
% 2.10/2.36  thf('65', plain,
% 2.10/2.36      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('split', [status(esa)], ['42'])).
% 2.10/2.36  thf('66', plain, ((r1_tarski @ sk_C @ sk_A)),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.36  thf('67', plain,
% 2.10/2.36      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('sup+', [status(thm)], ['65', '66'])).
% 2.10/2.36  thf(t3_xboole_1, axiom,
% 2.10/2.36    (![A:$i]:
% 2.10/2.36     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.10/2.36  thf('68', plain,
% 2.10/2.36      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 2.10/2.36      inference('cnf', [status(esa)], [t3_xboole_1])).
% 2.10/2.36  thf('69', plain,
% 2.10/2.36      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('sup-', [status(thm)], ['67', '68'])).
% 2.10/2.36  thf('70', plain,
% 2.10/2.36      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 2.10/2.36      inference('simplify', [status(thm)], ['47'])).
% 2.10/2.36  thf('71', plain,
% 2.10/2.36      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('demod', [status(thm)], ['46', '48'])).
% 2.10/2.36  thf('72', plain,
% 2.10/2.36      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('sup-', [status(thm)], ['67', '68'])).
% 2.10/2.36  thf('73', plain,
% 2.10/2.36      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('demod', [status(thm)], ['56', '61'])).
% 2.10/2.36  thf('74', plain,
% 2.10/2.36      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('sup-', [status(thm)], ['67', '68'])).
% 2.10/2.36  thf('75', plain,
% 2.10/2.36      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('demod', [status(thm)], ['46', '48'])).
% 2.10/2.36  thf('76', plain,
% 2.10/2.36      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 2.10/2.36      inference('simplify', [status(thm)], ['47'])).
% 2.10/2.36  thf('77', plain,
% 2.10/2.36      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.10/2.36         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 2.10/2.36          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.10/2.36      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.10/2.36  thf('78', plain,
% 2.10/2.36      (![X0 : $i, X1 : $i]:
% 2.10/2.36         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.10/2.36          | ((k1_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k1_relat_1 @ X1)))),
% 2.10/2.36      inference('sup-', [status(thm)], ['76', '77'])).
% 2.10/2.36  thf('79', plain,
% 2.10/2.36      ((![X0 : $i]:
% 2.10/2.36          ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_relat_1 @ sk_D)))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('sup-', [status(thm)], ['75', '78'])).
% 2.10/2.36  thf('80', plain,
% 2.10/2.36      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('split', [status(esa)], ['42'])).
% 2.10/2.36  thf('81', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.36  thf('82', plain,
% 2.10/2.36      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('sup+', [status(thm)], ['80', '81'])).
% 2.10/2.36  thf('83', plain,
% 2.10/2.36      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.10/2.36         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 2.10/2.36          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 2.10/2.36          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.10/2.36  thf('84', plain,
% 2.10/2.36      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 2.10/2.36         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('sup-', [status(thm)], ['82', '83'])).
% 2.10/2.36  thf('85', plain,
% 2.10/2.36      ((![X0 : $i]:
% 2.10/2.36          ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_relat_1 @ sk_D)))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('sup-', [status(thm)], ['75', '78'])).
% 2.10/2.36  thf('86', plain,
% 2.10/2.36      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 2.10/2.36         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('demod', [status(thm)], ['84', '85'])).
% 2.10/2.36  thf('87', plain,
% 2.10/2.36      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('demod', [status(thm)], ['46', '48'])).
% 2.10/2.36  thf('88', plain,
% 2.10/2.36      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 2.10/2.36      inference('simplify', [status(thm)], ['47'])).
% 2.10/2.36  thf('89', plain,
% 2.10/2.36      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.10/2.36         (~ (zip_tseitin_0 @ X36 @ X37)
% 2.10/2.36          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 2.10/2.36          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.10/2.36  thf('90', plain,
% 2.10/2.36      (![X0 : $i, X1 : $i]:
% 2.10/2.36         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.10/2.36          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 2.10/2.36          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 2.10/2.36      inference('sup-', [status(thm)], ['88', '89'])).
% 2.10/2.36  thf('91', plain,
% 2.10/2.36      (![X31 : $i, X32 : $i]:
% 2.10/2.36         ((zip_tseitin_0 @ X31 @ X32) | ((X32) != (k1_xboole_0)))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.10/2.36  thf('92', plain, (![X31 : $i]: (zip_tseitin_0 @ X31 @ k1_xboole_0)),
% 2.10/2.36      inference('simplify', [status(thm)], ['91'])).
% 2.10/2.36  thf('93', plain,
% 2.10/2.36      (![X0 : $i, X1 : $i]:
% 2.10/2.36         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.10/2.36          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 2.10/2.36      inference('demod', [status(thm)], ['90', '92'])).
% 2.10/2.36  thf('94', plain,
% 2.10/2.36      ((![X0 : $i]: (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('sup-', [status(thm)], ['87', '93'])).
% 2.10/2.36  thf('95', plain,
% 2.10/2.36      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('demod', [status(thm)], ['86', '94'])).
% 2.10/2.36  thf('96', plain,
% 2.10/2.36      ((![X0 : $i]: ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_xboole_0)))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('demod', [status(thm)], ['79', '95'])).
% 2.10/2.36  thf('97', plain,
% 2.10/2.36      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.10/2.36         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 2.10/2.36          | (v1_funct_2 @ X35 @ X33 @ X34)
% 2.10/2.36          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.10/2.36  thf('98', plain,
% 2.10/2.36      ((![X0 : $i]:
% 2.10/2.36          (((k1_xboole_0) != (k1_xboole_0))
% 2.10/2.36           | ~ (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0)
% 2.10/2.36           | (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0)))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('sup-', [status(thm)], ['96', '97'])).
% 2.10/2.36  thf('99', plain,
% 2.10/2.36      ((![X0 : $i]: (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('sup-', [status(thm)], ['87', '93'])).
% 2.10/2.36  thf('100', plain,
% 2.10/2.36      ((![X0 : $i]:
% 2.10/2.36          (((k1_xboole_0) != (k1_xboole_0))
% 2.10/2.36           | (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0)))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('demod', [status(thm)], ['98', '99'])).
% 2.10/2.36  thf('101', plain,
% 2.10/2.36      ((![X0 : $i]: (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0))
% 2.10/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.10/2.36      inference('simplify', [status(thm)], ['100'])).
% 2.10/2.36  thf('102', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 2.10/2.36      inference('demod', [status(thm)],
% 2.10/2.36                ['64', '69', '70', '71', '72', '73', '74', '101'])).
% 2.10/2.36  thf('103', plain,
% 2.10/2.36      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 2.10/2.36      inference('split', [status(esa)], ['42'])).
% 2.10/2.36  thf('104', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 2.10/2.36      inference('sat_resolution*', [status(thm)], ['102', '103'])).
% 2.10/2.36  thf('105', plain, (((sk_B) != (k1_xboole_0))),
% 2.10/2.36      inference('simpl_trail', [status(thm)], ['43', '104'])).
% 2.10/2.36  thf('106', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D))),
% 2.10/2.36      inference('simplify_reflect-', [status(thm)], ['41', '105'])).
% 2.10/2.36  thf('107', plain,
% 2.10/2.36      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 2.10/2.36      inference('sup+', [status(thm)], ['32', '106'])).
% 2.10/2.36  thf('108', plain, (((sk_B) != (k1_xboole_0))),
% 2.10/2.36      inference('simpl_trail', [status(thm)], ['43', '104'])).
% 2.10/2.36  thf('109', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 2.10/2.36      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 2.10/2.36  thf('110', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.10/2.36      inference('demod', [status(thm)], ['25', '109'])).
% 2.10/2.36  thf(t91_relat_1, axiom,
% 2.10/2.36    (![A:$i,B:$i]:
% 2.10/2.36     ( ( v1_relat_1 @ B ) =>
% 2.10/2.36       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 2.10/2.36         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 2.10/2.36  thf('111', plain,
% 2.10/2.36      (![X15 : $i, X16 : $i]:
% 2.10/2.36         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 2.10/2.36          | ((k1_relat_1 @ (k7_relat_1 @ X16 @ X15)) = (X15))
% 2.10/2.36          | ~ (v1_relat_1 @ X16))),
% 2.10/2.36      inference('cnf', [status(esa)], [t91_relat_1])).
% 2.10/2.36  thf('112', plain,
% 2.10/2.36      (![X0 : $i]:
% 2.10/2.36         (~ (r1_tarski @ X0 @ sk_A)
% 2.10/2.36          | ~ (v1_relat_1 @ sk_D)
% 2.10/2.36          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 2.10/2.36      inference('sup-', [status(thm)], ['110', '111'])).
% 2.10/2.36  thf('113', plain, ((v1_relat_1 @ sk_D)),
% 2.10/2.36      inference('demod', [status(thm)], ['59', '60'])).
% 2.10/2.36  thf('114', plain,
% 2.10/2.36      (![X0 : $i]:
% 2.10/2.36         (~ (r1_tarski @ X0 @ sk_A)
% 2.10/2.36          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 2.10/2.36      inference('demod', [status(thm)], ['112', '113'])).
% 2.10/2.36  thf('115', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 2.10/2.36      inference('sup-', [status(thm)], ['18', '114'])).
% 2.10/2.36  thf(t88_relat_1, axiom,
% 2.10/2.36    (![A:$i,B:$i]:
% 2.10/2.36     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 2.10/2.36  thf('116', plain,
% 2.10/2.36      (![X13 : $i, X14 : $i]:
% 2.10/2.36         ((r1_tarski @ (k7_relat_1 @ X13 @ X14) @ X13) | ~ (v1_relat_1 @ X13))),
% 2.10/2.36      inference('cnf', [status(esa)], [t88_relat_1])).
% 2.10/2.36  thf('117', plain,
% 2.10/2.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.36  thf(t4_relset_1, axiom,
% 2.10/2.36    (![A:$i,B:$i,C:$i,D:$i]:
% 2.10/2.36     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 2.10/2.36       ( ( r1_tarski @ A @ D ) =>
% 2.10/2.36         ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 2.10/2.36  thf('118', plain,
% 2.10/2.36      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 2.10/2.36         ((m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 2.10/2.36          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 2.10/2.36          | ~ (r1_tarski @ X27 @ X30))),
% 2.10/2.36      inference('cnf', [status(esa)], [t4_relset_1])).
% 2.10/2.36  thf('119', plain,
% 2.10/2.36      (![X0 : $i]:
% 2.10/2.36         (~ (r1_tarski @ X0 @ sk_D)
% 2.10/2.36          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 2.10/2.36      inference('sup-', [status(thm)], ['117', '118'])).
% 2.10/2.36  thf('120', plain,
% 2.10/2.36      (![X0 : $i]:
% 2.10/2.36         (~ (v1_relat_1 @ sk_D)
% 2.10/2.36          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 2.10/2.36             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 2.10/2.36      inference('sup-', [status(thm)], ['116', '119'])).
% 2.10/2.36  thf('121', plain, ((v1_relat_1 @ sk_D)),
% 2.10/2.36      inference('demod', [status(thm)], ['59', '60'])).
% 2.10/2.36  thf('122', plain,
% 2.10/2.36      (![X0 : $i]:
% 2.10/2.36         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 2.10/2.36          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.10/2.36      inference('demod', [status(thm)], ['120', '121'])).
% 2.10/2.36  thf('123', plain,
% 2.10/2.36      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 2.10/2.36         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 2.10/2.36          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 2.10/2.36          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 2.10/2.36      inference('cnf', [status(esa)], [t13_relset_1])).
% 2.10/2.36  thf('124', plain,
% 2.10/2.36      (![X0 : $i, X1 : $i]:
% 2.10/2.36         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 2.10/2.36           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.10/2.36          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 2.10/2.36      inference('sup-', [status(thm)], ['122', '123'])).
% 2.10/2.36  thf('125', plain,
% 2.10/2.36      (![X0 : $i]:
% 2.10/2.36         (~ (r1_tarski @ sk_C @ X0)
% 2.10/2.36          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 2.10/2.36             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B))))),
% 2.10/2.36      inference('sup-', [status(thm)], ['115', '124'])).
% 2.10/2.36  thf('126', plain,
% 2.10/2.36      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 2.10/2.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 2.10/2.36      inference('sup-', [status(thm)], ['17', '125'])).
% 2.10/2.36  thf('127', plain,
% 2.10/2.36      (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 2.10/2.36      inference('demod', [status(thm)], ['15', '126'])).
% 2.10/2.36  thf('128', plain,
% 2.10/2.36      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 2.10/2.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 2.10/2.36      inference('sup-', [status(thm)], ['17', '125'])).
% 2.10/2.36  thf('129', plain,
% 2.10/2.36      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.10/2.36         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 2.10/2.36          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.10/2.36      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.10/2.36  thf('130', plain,
% 2.10/2.36      (((k1_relset_1 @ sk_C @ sk_B @ (k7_relat_1 @ sk_D @ sk_C))
% 2.10/2.36         = (k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)))),
% 2.10/2.36      inference('sup-', [status(thm)], ['128', '129'])).
% 2.10/2.36  thf('131', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 2.10/2.36      inference('sup-', [status(thm)], ['18', '114'])).
% 2.10/2.36  thf('132', plain,
% 2.10/2.36      (((k1_relset_1 @ sk_C @ sk_B @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 2.10/2.36      inference('demod', [status(thm)], ['130', '131'])).
% 2.10/2.36  thf('133', plain,
% 2.10/2.36      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.10/2.36         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 2.10/2.36          | (v1_funct_2 @ X35 @ X33 @ X34)
% 2.10/2.36          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.10/2.36  thf('134', plain,
% 2.10/2.36      ((((sk_C) != (sk_C))
% 2.10/2.36        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)
% 2.10/2.36        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 2.10/2.36      inference('sup-', [status(thm)], ['132', '133'])).
% 2.10/2.36  thf('135', plain,
% 2.10/2.36      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 2.10/2.36        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C))),
% 2.10/2.36      inference('simplify', [status(thm)], ['134'])).
% 2.10/2.36  thf('136', plain,
% 2.10/2.36      (![X31 : $i, X32 : $i]:
% 2.10/2.36         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.10/2.36  thf('137', plain,
% 2.10/2.36      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 2.10/2.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 2.10/2.36      inference('sup-', [status(thm)], ['17', '125'])).
% 2.10/2.36  thf('138', plain,
% 2.10/2.36      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.10/2.36         (~ (zip_tseitin_0 @ X36 @ X37)
% 2.10/2.36          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 2.10/2.36          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 2.10/2.36      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.10/2.36  thf('139', plain,
% 2.10/2.36      (((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)
% 2.10/2.36        | ~ (zip_tseitin_0 @ sk_B @ sk_C))),
% 2.10/2.36      inference('sup-', [status(thm)], ['137', '138'])).
% 2.10/2.36  thf('140', plain,
% 2.10/2.36      ((((sk_B) = (k1_xboole_0))
% 2.10/2.36        | (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C))),
% 2.10/2.36      inference('sup-', [status(thm)], ['136', '139'])).
% 2.10/2.36  thf('141', plain, (((sk_B) != (k1_xboole_0))),
% 2.10/2.36      inference('simpl_trail', [status(thm)], ['43', '104'])).
% 2.10/2.36  thf('142', plain,
% 2.10/2.36      ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)),
% 2.10/2.36      inference('simplify_reflect-', [status(thm)], ['140', '141'])).
% 2.10/2.36  thf('143', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 2.10/2.36      inference('demod', [status(thm)], ['135', '142'])).
% 2.10/2.36  thf('144', plain, ($false), inference('demod', [status(thm)], ['127', '143'])).
% 2.10/2.36  
% 2.10/2.36  % SZS output end Refutation
% 2.10/2.36  
% 2.22/2.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
