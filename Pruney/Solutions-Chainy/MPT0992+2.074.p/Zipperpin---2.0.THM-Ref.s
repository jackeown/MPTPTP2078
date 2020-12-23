%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7v3rtvDbkF

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:45 EST 2020

% Result     : Theorem 36.27s
% Output     : Refutation 36.27s
% Verified   : 
% Statistics : Number of formulae       :  183 (1582 expanded)
%              Number of leaves         :   39 ( 468 expanded)
%              Depth                    :   25
%              Number of atoms          : 1404 (23429 expanded)
%              Number of equality atoms :  117 (1744 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X41 @ X42 @ X40 @ X43 ) ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ( ( k2_partfun1 @ X45 @ X46 @ X44 @ X47 )
        = ( k7_relat_1 @ X44 @ X47 ) ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

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
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('27',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('33',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('34',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','39'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('43',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('44',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('46',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('49',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('51',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('53',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('54',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ( ( k2_partfun1 @ X45 @ X46 @ X44 @ X47 )
        = ( k7_relat_1 @ X44 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('56',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X21 @ X22 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('57',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('60',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('61',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','62'])).

thf('64',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','63'])).

thf('65',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('66',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('67',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('68',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('69',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('70',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('71',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','63'])).

thf('72',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('73',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('74',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('77',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('78',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('79',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('80',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','81'])).

thf('83',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','60'])).

thf('84',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','84'])).

thf('86',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X33 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('90',plain,(
    ! [X32: $i] :
      ( zip_tseitin_0 @ X32 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('92',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['88','94'])).

thf('96',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['34','44','49','64','65','66','67','68','69','70','71','72','95'])).

thf('97',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('98',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['96','97'])).

thf('99',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['31','98'])).

thf('100',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['29','99'])).

thf('101',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('104',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('107',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['102','107'])).

thf('109',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('112',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X21 @ X22 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('114',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['105','106'])).

thf('118',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('120',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('121',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['109','122'])).

thf('124',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','123'])).

thf('125',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['13','124'])).

thf('126',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','123'])).

thf('127',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('128',plain,
    ( ( k1_relset_1 @ sk_C @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','108'])).

thf('130',plain,
    ( ( k1_relset_1 @ sk_C @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('132',plain,
    ( ( sk_C != sk_C )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('135',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','123'])).

thf('136',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('137',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['134','137'])).

thf('139',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['31','98'])).

thf('140',plain,(
    zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['133','140'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['125','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7v3rtvDbkF
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:31:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 36.27/36.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 36.27/36.49  % Solved by: fo/fo7.sh
% 36.27/36.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 36.27/36.49  % done 15656 iterations in 36.019s
% 36.27/36.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 36.27/36.49  % SZS output start Refutation
% 36.27/36.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 36.27/36.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 36.27/36.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 36.27/36.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 36.27/36.49  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 36.27/36.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 36.27/36.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 36.27/36.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 36.27/36.49  thf(sk_B_type, type, sk_B: $i).
% 36.27/36.49  thf(sk_C_type, type, sk_C: $i).
% 36.27/36.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 36.27/36.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 36.27/36.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 36.27/36.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 36.27/36.49  thf(sk_A_type, type, sk_A: $i).
% 36.27/36.49  thf(sk_D_type, type, sk_D: $i).
% 36.27/36.49  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 36.27/36.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 36.27/36.49  thf(t38_funct_2, conjecture,
% 36.27/36.49    (![A:$i,B:$i,C:$i,D:$i]:
% 36.27/36.49     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 36.27/36.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 36.27/36.49       ( ( r1_tarski @ C @ A ) =>
% 36.27/36.49         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 36.27/36.49           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 36.27/36.49             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 36.27/36.49             ( m1_subset_1 @
% 36.27/36.49               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 36.27/36.49               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 36.27/36.49  thf(zf_stmt_0, negated_conjecture,
% 36.27/36.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 36.27/36.49        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 36.27/36.49            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 36.27/36.49          ( ( r1_tarski @ C @ A ) =>
% 36.27/36.49            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 36.27/36.49              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 36.27/36.49                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 36.27/36.49                ( m1_subset_1 @
% 36.27/36.49                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 36.27/36.49                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 36.27/36.49    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 36.27/36.49  thf('0', plain,
% 36.27/36.49      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 36.27/36.49        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 36.27/36.49             sk_B)
% 36.27/36.49        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 36.27/36.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.27/36.49  thf('1', plain,
% 36.27/36.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.27/36.49  thf(dt_k2_partfun1, axiom,
% 36.27/36.49    (![A:$i,B:$i,C:$i,D:$i]:
% 36.27/36.49     ( ( ( v1_funct_1 @ C ) & 
% 36.27/36.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 36.27/36.49       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 36.27/36.49         ( m1_subset_1 @
% 36.27/36.49           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 36.27/36.49           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 36.27/36.49  thf('2', plain,
% 36.27/36.49      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 36.27/36.49         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 36.27/36.49          | ~ (v1_funct_1 @ X40)
% 36.27/36.49          | (v1_funct_1 @ (k2_partfun1 @ X41 @ X42 @ X40 @ X43)))),
% 36.27/36.49      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 36.27/36.49  thf('3', plain,
% 36.27/36.49      (![X0 : $i]:
% 36.27/36.49         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 36.27/36.49          | ~ (v1_funct_1 @ sk_D))),
% 36.27/36.49      inference('sup-', [status(thm)], ['1', '2'])).
% 36.27/36.49  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.27/36.49  thf('5', plain,
% 36.27/36.49      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 36.27/36.49      inference('demod', [status(thm)], ['3', '4'])).
% 36.27/36.49  thf('6', plain,
% 36.27/36.49      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 36.27/36.49        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 36.27/36.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 36.27/36.49      inference('demod', [status(thm)], ['0', '5'])).
% 36.27/36.49  thf('7', plain,
% 36.27/36.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.27/36.49  thf(redefinition_k2_partfun1, axiom,
% 36.27/36.49    (![A:$i,B:$i,C:$i,D:$i]:
% 36.27/36.49     ( ( ( v1_funct_1 @ C ) & 
% 36.27/36.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 36.27/36.49       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 36.27/36.49  thf('8', plain,
% 36.27/36.49      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 36.27/36.49         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 36.27/36.49          | ~ (v1_funct_1 @ X44)
% 36.27/36.49          | ((k2_partfun1 @ X45 @ X46 @ X44 @ X47) = (k7_relat_1 @ X44 @ X47)))),
% 36.27/36.49      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 36.27/36.49  thf('9', plain,
% 36.27/36.49      (![X0 : $i]:
% 36.27/36.49         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 36.27/36.49          | ~ (v1_funct_1 @ sk_D))),
% 36.27/36.49      inference('sup-', [status(thm)], ['7', '8'])).
% 36.27/36.49  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.27/36.49  thf('11', plain,
% 36.27/36.49      (![X0 : $i]:
% 36.27/36.49         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 36.27/36.49      inference('demod', [status(thm)], ['9', '10'])).
% 36.27/36.49  thf('12', plain,
% 36.27/36.49      (![X0 : $i]:
% 36.27/36.49         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 36.27/36.49      inference('demod', [status(thm)], ['9', '10'])).
% 36.27/36.49  thf('13', plain,
% 36.27/36.49      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 36.27/36.49        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 36.27/36.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 36.27/36.49      inference('demod', [status(thm)], ['6', '11', '12'])).
% 36.27/36.49  thf(d10_xboole_0, axiom,
% 36.27/36.49    (![A:$i,B:$i]:
% 36.27/36.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 36.27/36.49  thf('14', plain,
% 36.27/36.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 36.27/36.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 36.27/36.49  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 36.27/36.49      inference('simplify', [status(thm)], ['14'])).
% 36.27/36.49  thf('16', plain, ((r1_tarski @ sk_C @ sk_A)),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.27/36.49  thf(d1_funct_2, axiom,
% 36.27/36.49    (![A:$i,B:$i,C:$i]:
% 36.27/36.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 36.27/36.49       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 36.27/36.49           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 36.27/36.49             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 36.27/36.49         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 36.27/36.49           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 36.27/36.49             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 36.27/36.49  thf(zf_stmt_1, axiom,
% 36.27/36.49    (![B:$i,A:$i]:
% 36.27/36.49     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 36.27/36.49       ( zip_tseitin_0 @ B @ A ) ))).
% 36.27/36.49  thf('17', plain,
% 36.27/36.49      (![X32 : $i, X33 : $i]:
% 36.27/36.49         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 36.27/36.49  thf('18', plain,
% 36.27/36.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.27/36.49  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 36.27/36.49  thf(zf_stmt_3, axiom,
% 36.27/36.49    (![C:$i,B:$i,A:$i]:
% 36.27/36.49     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 36.27/36.49       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 36.27/36.49  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 36.27/36.49  thf(zf_stmt_5, axiom,
% 36.27/36.49    (![A:$i,B:$i,C:$i]:
% 36.27/36.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 36.27/36.49       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 36.27/36.49         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 36.27/36.49           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 36.27/36.49             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 36.27/36.49  thf('19', plain,
% 36.27/36.49      (![X37 : $i, X38 : $i, X39 : $i]:
% 36.27/36.49         (~ (zip_tseitin_0 @ X37 @ X38)
% 36.27/36.49          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 36.27/36.49          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 36.27/36.49  thf('20', plain,
% 36.27/36.49      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 36.27/36.49      inference('sup-', [status(thm)], ['18', '19'])).
% 36.27/36.49  thf('21', plain,
% 36.27/36.49      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 36.27/36.49      inference('sup-', [status(thm)], ['17', '20'])).
% 36.27/36.49  thf('22', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.27/36.49  thf('23', plain,
% 36.27/36.49      (![X34 : $i, X35 : $i, X36 : $i]:
% 36.27/36.49         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 36.27/36.49          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 36.27/36.49          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 36.27/36.49  thf('24', plain,
% 36.27/36.49      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 36.27/36.49        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 36.27/36.49      inference('sup-', [status(thm)], ['22', '23'])).
% 36.27/36.49  thf('25', plain,
% 36.27/36.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.27/36.49  thf(redefinition_k1_relset_1, axiom,
% 36.27/36.49    (![A:$i,B:$i,C:$i]:
% 36.27/36.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 36.27/36.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 36.27/36.49  thf('26', plain,
% 36.27/36.49      (![X25 : $i, X26 : $i, X27 : $i]:
% 36.27/36.49         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 36.27/36.49          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 36.27/36.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 36.27/36.49  thf('27', plain,
% 36.27/36.49      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 36.27/36.49      inference('sup-', [status(thm)], ['25', '26'])).
% 36.27/36.49  thf('28', plain,
% 36.27/36.49      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 36.27/36.49      inference('demod', [status(thm)], ['24', '27'])).
% 36.27/36.49  thf('29', plain,
% 36.27/36.49      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 36.27/36.49      inference('sup-', [status(thm)], ['21', '28'])).
% 36.27/36.49  thf('30', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.27/36.49  thf('31', plain,
% 36.27/36.49      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 36.27/36.49      inference('split', [status(esa)], ['30'])).
% 36.27/36.49  thf('32', plain,
% 36.27/36.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('split', [status(esa)], ['30'])).
% 36.27/36.49  thf('33', plain,
% 36.27/36.49      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 36.27/36.49        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 36.27/36.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 36.27/36.49      inference('demod', [status(thm)], ['0', '5'])).
% 36.27/36.49  thf('34', plain,
% 36.27/36.49      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 36.27/36.49            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 36.27/36.49         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 36.27/36.49              sk_B)))
% 36.27/36.49         <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('sup-', [status(thm)], ['32', '33'])).
% 36.27/36.49  thf('35', plain,
% 36.27/36.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('split', [status(esa)], ['30'])).
% 36.27/36.49  thf('36', plain,
% 36.27/36.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.27/36.49  thf('37', plain,
% 36.27/36.49      (((m1_subset_1 @ sk_D @ 
% 36.27/36.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 36.27/36.49         <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('sup+', [status(thm)], ['35', '36'])).
% 36.27/36.49  thf(t113_zfmisc_1, axiom,
% 36.27/36.49    (![A:$i,B:$i]:
% 36.27/36.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 36.27/36.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 36.27/36.49  thf('38', plain,
% 36.27/36.49      (![X8 : $i, X9 : $i]:
% 36.27/36.49         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 36.27/36.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 36.27/36.49  thf('39', plain,
% 36.27/36.49      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 36.27/36.49      inference('simplify', [status(thm)], ['38'])).
% 36.27/36.49  thf('40', plain,
% 36.27/36.49      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 36.27/36.49         <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('demod', [status(thm)], ['37', '39'])).
% 36.27/36.49  thf(t3_subset, axiom,
% 36.27/36.49    (![A:$i,B:$i]:
% 36.27/36.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 36.27/36.49  thf('41', plain,
% 36.27/36.49      (![X11 : $i, X12 : $i]:
% 36.27/36.49         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 36.27/36.49      inference('cnf', [status(esa)], [t3_subset])).
% 36.27/36.49  thf('42', plain,
% 36.27/36.49      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('sup-', [status(thm)], ['40', '41'])).
% 36.27/36.49  thf(t3_xboole_1, axiom,
% 36.27/36.49    (![A:$i]:
% 36.27/36.49     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 36.27/36.49  thf('43', plain,
% 36.27/36.49      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 36.27/36.49      inference('cnf', [status(esa)], [t3_xboole_1])).
% 36.27/36.49  thf('44', plain,
% 36.27/36.49      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('sup-', [status(thm)], ['42', '43'])).
% 36.27/36.49  thf('45', plain,
% 36.27/36.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('split', [status(esa)], ['30'])).
% 36.27/36.49  thf('46', plain, ((r1_tarski @ sk_C @ sk_A)),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.27/36.49  thf('47', plain,
% 36.27/36.49      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('sup+', [status(thm)], ['45', '46'])).
% 36.27/36.49  thf('48', plain,
% 36.27/36.49      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 36.27/36.49      inference('cnf', [status(esa)], [t3_xboole_1])).
% 36.27/36.49  thf('49', plain,
% 36.27/36.49      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('sup-', [status(thm)], ['47', '48'])).
% 36.27/36.49  thf('50', plain,
% 36.27/36.49      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('sup-', [status(thm)], ['42', '43'])).
% 36.27/36.49  thf('51', plain, ((v1_funct_1 @ sk_D)),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.27/36.49  thf('52', plain,
% 36.27/36.49      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('sup+', [status(thm)], ['50', '51'])).
% 36.27/36.49  thf(t4_subset_1, axiom,
% 36.27/36.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 36.27/36.49  thf('53', plain,
% 36.27/36.49      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 36.27/36.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 36.27/36.49  thf('54', plain,
% 36.27/36.49      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 36.27/36.49         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 36.27/36.49          | ~ (v1_funct_1 @ X44)
% 36.27/36.49          | ((k2_partfun1 @ X45 @ X46 @ X44 @ X47) = (k7_relat_1 @ X44 @ X47)))),
% 36.27/36.49      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 36.27/36.49  thf('55', plain,
% 36.27/36.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.27/36.49         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 36.27/36.49            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 36.27/36.49          | ~ (v1_funct_1 @ k1_xboole_0))),
% 36.27/36.49      inference('sup-', [status(thm)], ['53', '54'])).
% 36.27/36.49  thf(t88_relat_1, axiom,
% 36.27/36.49    (![A:$i,B:$i]:
% 36.27/36.49     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 36.27/36.49  thf('56', plain,
% 36.27/36.49      (![X21 : $i, X22 : $i]:
% 36.27/36.49         ((r1_tarski @ (k7_relat_1 @ X21 @ X22) @ X21) | ~ (v1_relat_1 @ X21))),
% 36.27/36.49      inference('cnf', [status(esa)], [t88_relat_1])).
% 36.27/36.49  thf('57', plain,
% 36.27/36.49      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 36.27/36.49      inference('cnf', [status(esa)], [t3_xboole_1])).
% 36.27/36.49  thf('58', plain,
% 36.27/36.49      (![X0 : $i]:
% 36.27/36.49         (~ (v1_relat_1 @ k1_xboole_0)
% 36.27/36.49          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 36.27/36.49      inference('sup-', [status(thm)], ['56', '57'])).
% 36.27/36.49  thf('59', plain,
% 36.27/36.49      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 36.27/36.49      inference('simplify', [status(thm)], ['38'])).
% 36.27/36.49  thf(fc6_relat_1, axiom,
% 36.27/36.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 36.27/36.49  thf('60', plain,
% 36.27/36.49      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 36.27/36.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 36.27/36.49  thf('61', plain, ((v1_relat_1 @ k1_xboole_0)),
% 36.27/36.49      inference('sup+', [status(thm)], ['59', '60'])).
% 36.27/36.49  thf('62', plain,
% 36.27/36.49      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 36.27/36.49      inference('demod', [status(thm)], ['58', '61'])).
% 36.27/36.49  thf('63', plain,
% 36.27/36.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.27/36.49         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 36.27/36.49          | ~ (v1_funct_1 @ k1_xboole_0))),
% 36.27/36.49      inference('demod', [status(thm)], ['55', '62'])).
% 36.27/36.49  thf('64', plain,
% 36.27/36.49      ((![X0 : $i, X1 : $i, X2 : $i]:
% 36.27/36.49          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 36.27/36.49         <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('sup-', [status(thm)], ['52', '63'])).
% 36.27/36.49  thf('65', plain,
% 36.27/36.49      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('sup-', [status(thm)], ['47', '48'])).
% 36.27/36.49  thf('66', plain,
% 36.27/36.49      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 36.27/36.49      inference('simplify', [status(thm)], ['38'])).
% 36.27/36.49  thf('67', plain,
% 36.27/36.49      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 36.27/36.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 36.27/36.49  thf('68', plain,
% 36.27/36.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('split', [status(esa)], ['30'])).
% 36.27/36.49  thf('69', plain,
% 36.27/36.49      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('sup-', [status(thm)], ['42', '43'])).
% 36.27/36.49  thf('70', plain,
% 36.27/36.49      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('sup-', [status(thm)], ['47', '48'])).
% 36.27/36.49  thf('71', plain,
% 36.27/36.49      ((![X0 : $i, X1 : $i, X2 : $i]:
% 36.27/36.49          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 36.27/36.49         <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('sup-', [status(thm)], ['52', '63'])).
% 36.27/36.49  thf('72', plain,
% 36.27/36.49      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.27/36.49      inference('sup-', [status(thm)], ['47', '48'])).
% 36.27/36.49  thf('73', plain,
% 36.27/36.49      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 36.27/36.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 36.27/36.49  thf('74', plain,
% 36.27/36.49      (![X25 : $i, X26 : $i, X27 : $i]:
% 36.27/36.49         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 36.27/36.49          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 36.27/36.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 36.27/36.49  thf('75', plain,
% 36.27/36.49      (![X0 : $i, X1 : $i]:
% 36.27/36.49         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 36.27/36.49      inference('sup-', [status(thm)], ['73', '74'])).
% 36.27/36.49  thf('76', plain,
% 36.27/36.49      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 36.27/36.49      inference('demod', [status(thm)], ['58', '61'])).
% 36.27/36.49  thf('77', plain,
% 36.27/36.49      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 36.27/36.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 36.27/36.49  thf('78', plain,
% 36.27/36.49      (![X11 : $i, X12 : $i]:
% 36.27/36.49         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 36.27/36.49      inference('cnf', [status(esa)], [t3_subset])).
% 36.27/36.49  thf('79', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 36.27/36.49      inference('sup-', [status(thm)], ['77', '78'])).
% 36.27/36.49  thf(t91_relat_1, axiom,
% 36.27/36.49    (![A:$i,B:$i]:
% 36.27/36.49     ( ( v1_relat_1 @ B ) =>
% 36.27/36.49       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 36.27/36.49         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 36.27/36.49  thf('80', plain,
% 36.27/36.49      (![X23 : $i, X24 : $i]:
% 36.27/36.49         (~ (r1_tarski @ X23 @ (k1_relat_1 @ X24))
% 36.27/36.49          | ((k1_relat_1 @ (k7_relat_1 @ X24 @ X23)) = (X23))
% 36.27/36.49          | ~ (v1_relat_1 @ X24))),
% 36.27/36.49      inference('cnf', [status(esa)], [t91_relat_1])).
% 36.27/36.49  thf('81', plain,
% 36.27/36.49      (![X0 : $i]:
% 36.27/36.49         (~ (v1_relat_1 @ X0)
% 36.27/36.49          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 36.27/36.49      inference('sup-', [status(thm)], ['79', '80'])).
% 36.27/36.49  thf('82', plain,
% 36.27/36.49      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 36.27/36.49        | ~ (v1_relat_1 @ k1_xboole_0))),
% 36.27/36.49      inference('sup+', [status(thm)], ['76', '81'])).
% 36.27/36.49  thf('83', plain, ((v1_relat_1 @ k1_xboole_0)),
% 36.27/36.49      inference('sup+', [status(thm)], ['59', '60'])).
% 36.27/36.49  thf('84', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 36.27/36.49      inference('demod', [status(thm)], ['82', '83'])).
% 36.27/36.49  thf('85', plain,
% 36.27/36.49      (![X0 : $i, X1 : $i]:
% 36.27/36.49         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 36.27/36.49      inference('demod', [status(thm)], ['75', '84'])).
% 36.27/36.49  thf('86', plain,
% 36.27/36.49      (![X34 : $i, X35 : $i, X36 : $i]:
% 36.27/36.49         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 36.27/36.49          | (v1_funct_2 @ X36 @ X34 @ X35)
% 36.27/36.49          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 36.27/36.49  thf('87', plain,
% 36.27/36.49      (![X0 : $i, X1 : $i]:
% 36.27/36.49         (((X1) != (k1_xboole_0))
% 36.27/36.49          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 36.27/36.49          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 36.27/36.49      inference('sup-', [status(thm)], ['85', '86'])).
% 36.27/36.49  thf('88', plain,
% 36.27/36.49      (![X0 : $i]:
% 36.27/36.49         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 36.27/36.49          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 36.27/36.49      inference('simplify', [status(thm)], ['87'])).
% 36.27/36.49  thf('89', plain,
% 36.27/36.49      (![X32 : $i, X33 : $i]:
% 36.27/36.49         ((zip_tseitin_0 @ X32 @ X33) | ((X33) != (k1_xboole_0)))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 36.27/36.49  thf('90', plain, (![X32 : $i]: (zip_tseitin_0 @ X32 @ k1_xboole_0)),
% 36.27/36.49      inference('simplify', [status(thm)], ['89'])).
% 36.27/36.49  thf('91', plain,
% 36.27/36.49      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 36.27/36.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 36.27/36.49  thf('92', plain,
% 36.27/36.49      (![X37 : $i, X38 : $i, X39 : $i]:
% 36.27/36.49         (~ (zip_tseitin_0 @ X37 @ X38)
% 36.27/36.49          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 36.27/36.49          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 36.27/36.49  thf('93', plain,
% 36.27/36.49      (![X0 : $i, X1 : $i]:
% 36.27/36.49         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 36.27/36.49      inference('sup-', [status(thm)], ['91', '92'])).
% 36.27/36.49  thf('94', plain,
% 36.27/36.49      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 36.27/36.49      inference('sup-', [status(thm)], ['90', '93'])).
% 36.27/36.49  thf('95', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 36.27/36.49      inference('demod', [status(thm)], ['88', '94'])).
% 36.27/36.49  thf('96', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 36.27/36.49      inference('demod', [status(thm)],
% 36.27/36.49                ['34', '44', '49', '64', '65', '66', '67', '68', '69', '70', 
% 36.27/36.49                 '71', '72', '95'])).
% 36.27/36.49  thf('97', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 36.27/36.49      inference('split', [status(esa)], ['30'])).
% 36.27/36.49  thf('98', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 36.27/36.49      inference('sat_resolution*', [status(thm)], ['96', '97'])).
% 36.27/36.49  thf('99', plain, (((sk_B) != (k1_xboole_0))),
% 36.27/36.49      inference('simpl_trail', [status(thm)], ['31', '98'])).
% 36.27/36.49  thf('100', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 36.27/36.49      inference('simplify_reflect-', [status(thm)], ['29', '99'])).
% 36.27/36.49  thf('101', plain,
% 36.27/36.49      (![X23 : $i, X24 : $i]:
% 36.27/36.49         (~ (r1_tarski @ X23 @ (k1_relat_1 @ X24))
% 36.27/36.49          | ((k1_relat_1 @ (k7_relat_1 @ X24 @ X23)) = (X23))
% 36.27/36.49          | ~ (v1_relat_1 @ X24))),
% 36.27/36.49      inference('cnf', [status(esa)], [t91_relat_1])).
% 36.27/36.49  thf('102', plain,
% 36.27/36.49      (![X0 : $i]:
% 36.27/36.49         (~ (r1_tarski @ X0 @ sk_A)
% 36.27/36.49          | ~ (v1_relat_1 @ sk_D)
% 36.27/36.49          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 36.27/36.49      inference('sup-', [status(thm)], ['100', '101'])).
% 36.27/36.49  thf('103', plain,
% 36.27/36.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.27/36.49  thf(cc2_relat_1, axiom,
% 36.27/36.49    (![A:$i]:
% 36.27/36.49     ( ( v1_relat_1 @ A ) =>
% 36.27/36.49       ( ![B:$i]:
% 36.27/36.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 36.27/36.49  thf('104', plain,
% 36.27/36.49      (![X17 : $i, X18 : $i]:
% 36.27/36.49         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 36.27/36.49          | (v1_relat_1 @ X17)
% 36.27/36.49          | ~ (v1_relat_1 @ X18))),
% 36.27/36.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 36.27/36.49  thf('105', plain,
% 36.27/36.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 36.27/36.49      inference('sup-', [status(thm)], ['103', '104'])).
% 36.27/36.49  thf('106', plain,
% 36.27/36.49      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 36.27/36.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 36.27/36.49  thf('107', plain, ((v1_relat_1 @ sk_D)),
% 36.27/36.49      inference('demod', [status(thm)], ['105', '106'])).
% 36.27/36.49  thf('108', plain,
% 36.27/36.49      (![X0 : $i]:
% 36.27/36.49         (~ (r1_tarski @ X0 @ sk_A)
% 36.27/36.49          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 36.27/36.49      inference('demod', [status(thm)], ['102', '107'])).
% 36.27/36.49  thf('109', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 36.27/36.49      inference('sup-', [status(thm)], ['16', '108'])).
% 36.27/36.49  thf('110', plain,
% 36.27/36.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.27/36.49  thf('111', plain,
% 36.27/36.49      (![X11 : $i, X12 : $i]:
% 36.27/36.49         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 36.27/36.49      inference('cnf', [status(esa)], [t3_subset])).
% 36.27/36.49  thf('112', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 36.27/36.49      inference('sup-', [status(thm)], ['110', '111'])).
% 36.27/36.49  thf('113', plain,
% 36.27/36.49      (![X21 : $i, X22 : $i]:
% 36.27/36.49         ((r1_tarski @ (k7_relat_1 @ X21 @ X22) @ X21) | ~ (v1_relat_1 @ X21))),
% 36.27/36.49      inference('cnf', [status(esa)], [t88_relat_1])).
% 36.27/36.49  thf(t1_xboole_1, axiom,
% 36.27/36.49    (![A:$i,B:$i,C:$i]:
% 36.27/36.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 36.27/36.49       ( r1_tarski @ A @ C ) ))).
% 36.27/36.49  thf('114', plain,
% 36.27/36.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 36.27/36.49         (~ (r1_tarski @ X3 @ X4)
% 36.27/36.49          | ~ (r1_tarski @ X4 @ X5)
% 36.27/36.49          | (r1_tarski @ X3 @ X5))),
% 36.27/36.49      inference('cnf', [status(esa)], [t1_xboole_1])).
% 36.27/36.49  thf('115', plain,
% 36.27/36.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.27/36.49         (~ (v1_relat_1 @ X0)
% 36.27/36.49          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 36.27/36.49          | ~ (r1_tarski @ X0 @ X2))),
% 36.27/36.49      inference('sup-', [status(thm)], ['113', '114'])).
% 36.27/36.49  thf('116', plain,
% 36.27/36.49      (![X0 : $i]:
% 36.27/36.49         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 36.27/36.49          | ~ (v1_relat_1 @ sk_D))),
% 36.27/36.49      inference('sup-', [status(thm)], ['112', '115'])).
% 36.27/36.49  thf('117', plain, ((v1_relat_1 @ sk_D)),
% 36.27/36.49      inference('demod', [status(thm)], ['105', '106'])).
% 36.27/36.49  thf('118', plain,
% 36.27/36.49      (![X0 : $i]:
% 36.27/36.49         (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 36.27/36.49      inference('demod', [status(thm)], ['116', '117'])).
% 36.27/36.49  thf('119', plain,
% 36.27/36.49      (![X11 : $i, X13 : $i]:
% 36.27/36.49         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 36.27/36.49      inference('cnf', [status(esa)], [t3_subset])).
% 36.27/36.49  thf('120', plain,
% 36.27/36.49      (![X0 : $i]:
% 36.27/36.49         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 36.27/36.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.27/36.49      inference('sup-', [status(thm)], ['118', '119'])).
% 36.27/36.49  thf(t13_relset_1, axiom,
% 36.27/36.49    (![A:$i,B:$i,C:$i,D:$i]:
% 36.27/36.49     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 36.27/36.49       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 36.27/36.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 36.27/36.49  thf('121', plain,
% 36.27/36.49      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 36.27/36.49         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 36.27/36.49          | (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 36.27/36.49          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 36.27/36.49      inference('cnf', [status(esa)], [t13_relset_1])).
% 36.27/36.49  thf('122', plain,
% 36.27/36.49      (![X0 : $i, X1 : $i]:
% 36.27/36.49         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 36.27/36.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 36.27/36.49          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 36.27/36.49      inference('sup-', [status(thm)], ['120', '121'])).
% 36.27/36.49  thf('123', plain,
% 36.27/36.49      (![X0 : $i]:
% 36.27/36.49         (~ (r1_tarski @ sk_C @ X0)
% 36.27/36.49          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 36.27/36.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B))))),
% 36.27/36.49      inference('sup-', [status(thm)], ['109', '122'])).
% 36.27/36.49  thf('124', plain,
% 36.27/36.49      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 36.27/36.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 36.27/36.49      inference('sup-', [status(thm)], ['15', '123'])).
% 36.27/36.49  thf('125', plain,
% 36.27/36.49      (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 36.27/36.49      inference('demod', [status(thm)], ['13', '124'])).
% 36.27/36.49  thf('126', plain,
% 36.27/36.49      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 36.27/36.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 36.27/36.49      inference('sup-', [status(thm)], ['15', '123'])).
% 36.27/36.49  thf('127', plain,
% 36.27/36.49      (![X25 : $i, X26 : $i, X27 : $i]:
% 36.27/36.49         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 36.27/36.49          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 36.27/36.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 36.27/36.49  thf('128', plain,
% 36.27/36.49      (((k1_relset_1 @ sk_C @ sk_B @ (k7_relat_1 @ sk_D @ sk_C))
% 36.27/36.49         = (k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)))),
% 36.27/36.49      inference('sup-', [status(thm)], ['126', '127'])).
% 36.27/36.49  thf('129', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 36.27/36.49      inference('sup-', [status(thm)], ['16', '108'])).
% 36.27/36.49  thf('130', plain,
% 36.27/36.49      (((k1_relset_1 @ sk_C @ sk_B @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 36.27/36.49      inference('demod', [status(thm)], ['128', '129'])).
% 36.27/36.49  thf('131', plain,
% 36.27/36.49      (![X34 : $i, X35 : $i, X36 : $i]:
% 36.27/36.49         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 36.27/36.49          | (v1_funct_2 @ X36 @ X34 @ X35)
% 36.27/36.49          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 36.27/36.49  thf('132', plain,
% 36.27/36.49      ((((sk_C) != (sk_C))
% 36.27/36.49        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)
% 36.27/36.49        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 36.27/36.49      inference('sup-', [status(thm)], ['130', '131'])).
% 36.27/36.49  thf('133', plain,
% 36.27/36.49      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 36.27/36.49        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C))),
% 36.27/36.49      inference('simplify', [status(thm)], ['132'])).
% 36.27/36.49  thf('134', plain,
% 36.27/36.49      (![X32 : $i, X33 : $i]:
% 36.27/36.49         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 36.27/36.49  thf('135', plain,
% 36.27/36.49      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 36.27/36.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 36.27/36.49      inference('sup-', [status(thm)], ['15', '123'])).
% 36.27/36.49  thf('136', plain,
% 36.27/36.49      (![X37 : $i, X38 : $i, X39 : $i]:
% 36.27/36.49         (~ (zip_tseitin_0 @ X37 @ X38)
% 36.27/36.49          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 36.27/36.49          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 36.27/36.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 36.27/36.49  thf('137', plain,
% 36.27/36.49      (((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)
% 36.27/36.49        | ~ (zip_tseitin_0 @ sk_B @ sk_C))),
% 36.27/36.49      inference('sup-', [status(thm)], ['135', '136'])).
% 36.27/36.49  thf('138', plain,
% 36.27/36.49      ((((sk_B) = (k1_xboole_0))
% 36.27/36.49        | (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C))),
% 36.27/36.49      inference('sup-', [status(thm)], ['134', '137'])).
% 36.27/36.49  thf('139', plain, (((sk_B) != (k1_xboole_0))),
% 36.27/36.49      inference('simpl_trail', [status(thm)], ['31', '98'])).
% 36.27/36.49  thf('140', plain,
% 36.27/36.49      ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)),
% 36.27/36.49      inference('simplify_reflect-', [status(thm)], ['138', '139'])).
% 36.27/36.49  thf('141', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 36.27/36.49      inference('demod', [status(thm)], ['133', '140'])).
% 36.27/36.49  thf('142', plain, ($false), inference('demod', [status(thm)], ['125', '141'])).
% 36.27/36.49  
% 36.27/36.49  % SZS output end Refutation
% 36.27/36.49  
% 36.27/36.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
