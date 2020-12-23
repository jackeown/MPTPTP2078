%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LeMjl8RNBD

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:05 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  222 ( 846 expanded)
%              Number of leaves         :   50 ( 261 expanded)
%              Depth                    :   32
%              Number of atoms          : 1488 (10110 expanded)
%              Number of equality atoms :   91 ( 678 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X41 @ X39 )
        = ( k2_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_2 ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X42 ) @ X43 )
      | ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['4','15','16'])).

thf('18',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['1','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X37 @ X38 @ X36 )
        = ( k1_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('21',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_2 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
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

thf('23',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( v1_funct_2 @ X56 @ X54 @ X55 )
      | ( X54
        = ( k1_relset_1 @ X54 @ X55 @ X56 ) )
      | ~ ( zip_tseitin_1 @ X56 @ X55 @ X54 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X37 @ X38 @ X36 )
        = ( k1_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('27',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X52: $i,X53: $i] :
      ( ( zip_tseitin_0 @ X52 @ X53 )
      | ( X52 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('31',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( zip_tseitin_0 @ X57 @ X58 )
      | ( zip_tseitin_1 @ X59 @ X57 @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('32',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('44',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_xboole_0 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X51 ) ) )
      | ( v1_partfun1 @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('45',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('46',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('47',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('48',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','51'])).

thf('53',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('55',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ( r2_hidden @ ( sk_B @ sk_D ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('65',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','49'])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('68',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('69',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('73',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('74',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('75',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_partfun1 @ X46 @ X47 )
      | ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_partfun1 @ k1_xboole_0 @ X0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','77'])).

thf('79',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('80',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('81',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_2 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('86',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('89',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_2 ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','49'])).

thf('94',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('97',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','84','94','95','96'])).

thf('98',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['35','97'])).

thf('99',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['33','98'])).

thf('100',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['28','99'])).

thf('101',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_2 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['21','100'])).

thf('102',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( X54
       != ( k1_relset_1 @ X54 @ X55 @ X56 ) )
      | ( v1_funct_2 @ X56 @ X54 @ X55 )
      | ~ ( zip_tseitin_1 @ X56 @ X55 @ X54 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('103',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_2 @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('105',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( zip_tseitin_0 @ X57 @ X58 )
      | ( zip_tseitin_1 @ X59 @ X57 @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('106',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X52: $i,X53: $i] :
      ( ( zip_tseitin_0 @ X52 @ X53 )
      | ( X52 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('108',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','49'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('112',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('113',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( v1_xboole_0 @ X20 )
      | ~ ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('114',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('116',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C_2 @ X0 )
      | ( v1_xboole_0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['109','116'])).

thf('118',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('119',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('121',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('123',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X16 @ X14 ) @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X1 ) @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['119','124'])).

thf('126',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( v1_xboole_0 @ X20 )
      | ~ ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','49'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['28','99'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('133',plain,(
    ! [X27: $i] :
      ( ( r1_tarski @ X27 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X27 ) @ ( k2_relat_1 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('134',plain,
    ( ( r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('136',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('137',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['134','137'])).

thf('139',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('140',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( v1_xboole_0 @ X20 )
      | ~ ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('142',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_D ) ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['131','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C_2 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['117','143'])).

thf('145',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['28','99'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('147',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('149',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('150',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v4_relat_1 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('151',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v4_relat_1 @ X25 @ X26 )
      | ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('154',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('155',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(clc,[status(thm)],['152','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['145','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C_2 @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['144','159'])).

thf('161',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('162',plain,(
    ! [X52: $i,X53: $i] :
      ( ( zip_tseitin_0 @ X52 @ X53 )
      | ( X53 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('163',plain,(
    ! [X52: $i] :
      ( zip_tseitin_0 @ X52 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['161','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C_2 @ X1 )
      | ( zip_tseitin_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['160','164'])).

thf('166',plain,(
    zip_tseitin_0 @ sk_C_2 @ sk_A ),
    inference(eq_fact,[status(thm)],['165'])).

thf('167',plain,(
    zip_tseitin_1 @ sk_D @ sk_C_2 @ sk_A ),
    inference(demod,[status(thm)],['106','166'])).

thf('168',plain,
    ( ( sk_A != sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['103','167'])).

thf('169',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_C_2 ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    $false ),
    inference(demod,[status(thm)],['18','169'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LeMjl8RNBD
% 0.13/0.36  % Computer   : n007.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 09:46:51 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 1.44/1.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.44/1.67  % Solved by: fo/fo7.sh
% 1.44/1.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.44/1.67  % done 1539 iterations in 1.186s
% 1.44/1.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.44/1.67  % SZS output start Refutation
% 1.44/1.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.44/1.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.44/1.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.44/1.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.44/1.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.44/1.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.44/1.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.44/1.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.44/1.67  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.44/1.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.44/1.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.44/1.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.44/1.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.44/1.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.44/1.67  thf(sk_B_type, type, sk_B: $i > $i).
% 1.44/1.67  thf(sk_D_type, type, sk_D: $i).
% 1.44/1.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.44/1.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.44/1.67  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.44/1.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.44/1.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.44/1.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.44/1.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.44/1.67  thf(sk_A_type, type, sk_A: $i).
% 1.44/1.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.44/1.67  thf(t8_funct_2, conjecture,
% 1.44/1.67    (![A:$i,B:$i,C:$i,D:$i]:
% 1.44/1.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.44/1.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.44/1.67       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.44/1.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.44/1.67           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.44/1.67             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 1.44/1.67  thf(zf_stmt_0, negated_conjecture,
% 1.44/1.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.44/1.67        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.44/1.67            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.44/1.67          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.44/1.67            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.44/1.67              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.44/1.67                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 1.44/1.67    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 1.44/1.67  thf('0', plain,
% 1.44/1.67      ((~ (v1_funct_1 @ sk_D)
% 1.44/1.67        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_2)
% 1.44/1.67        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2))))),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.67  thf('1', plain,
% 1.44/1.67      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_2))
% 1.44/1.67         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_2)))),
% 1.44/1.67      inference('split', [status(esa)], ['0'])).
% 1.44/1.67  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.67  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 1.44/1.67      inference('split', [status(esa)], ['0'])).
% 1.44/1.67  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 1.44/1.67      inference('sup-', [status(thm)], ['2', '3'])).
% 1.44/1.67  thf('5', plain,
% 1.44/1.67      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ sk_C_2)),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.67  thf('6', plain,
% 1.44/1.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.67  thf(redefinition_k2_relset_1, axiom,
% 1.44/1.67    (![A:$i,B:$i,C:$i]:
% 1.44/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.44/1.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.44/1.67  thf('7', plain,
% 1.44/1.67      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.44/1.67         (((k2_relset_1 @ X40 @ X41 @ X39) = (k2_relat_1 @ X39))
% 1.44/1.67          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 1.44/1.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.44/1.67  thf('8', plain,
% 1.44/1.67      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.44/1.67      inference('sup-', [status(thm)], ['6', '7'])).
% 1.44/1.67  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_2)),
% 1.44/1.67      inference('demod', [status(thm)], ['5', '8'])).
% 1.44/1.67  thf('10', plain,
% 1.44/1.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.67  thf(t14_relset_1, axiom,
% 1.44/1.67    (![A:$i,B:$i,C:$i,D:$i]:
% 1.44/1.67     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.44/1.67       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 1.44/1.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 1.44/1.67  thf('11', plain,
% 1.44/1.67      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 1.44/1.67         (~ (r1_tarski @ (k2_relat_1 @ X42) @ X43)
% 1.44/1.67          | (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 1.44/1.67          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 1.44/1.67      inference('cnf', [status(esa)], [t14_relset_1])).
% 1.44/1.67  thf('12', plain,
% 1.44/1.67      (![X0 : $i]:
% 1.44/1.67         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.44/1.67          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 1.44/1.67      inference('sup-', [status(thm)], ['10', '11'])).
% 1.44/1.67  thf('13', plain,
% 1.44/1.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2)))),
% 1.44/1.67      inference('sup-', [status(thm)], ['9', '12'])).
% 1.44/1.67  thf('14', plain,
% 1.44/1.67      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2))))
% 1.44/1.67         <= (~
% 1.44/1.67             ((m1_subset_1 @ sk_D @ 
% 1.44/1.67               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2)))))),
% 1.44/1.67      inference('split', [status(esa)], ['0'])).
% 1.44/1.67  thf('15', plain,
% 1.44/1.67      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2))))),
% 1.44/1.67      inference('sup-', [status(thm)], ['13', '14'])).
% 1.44/1.67  thf('16', plain,
% 1.44/1.67      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_2)) | 
% 1.44/1.67       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2)))) | 
% 1.44/1.67       ~ ((v1_funct_1 @ sk_D))),
% 1.44/1.67      inference('split', [status(esa)], ['0'])).
% 1.44/1.67  thf('17', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_2))),
% 1.44/1.67      inference('sat_resolution*', [status(thm)], ['4', '15', '16'])).
% 1.44/1.67  thf('18', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_2)),
% 1.44/1.67      inference('simpl_trail', [status(thm)], ['1', '17'])).
% 1.44/1.67  thf('19', plain,
% 1.44/1.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2)))),
% 1.44/1.67      inference('sup-', [status(thm)], ['9', '12'])).
% 1.44/1.67  thf(redefinition_k1_relset_1, axiom,
% 1.44/1.67    (![A:$i,B:$i,C:$i]:
% 1.44/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.44/1.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.44/1.67  thf('20', plain,
% 1.44/1.67      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.44/1.67         (((k1_relset_1 @ X37 @ X38 @ X36) = (k1_relat_1 @ X36))
% 1.44/1.67          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 1.44/1.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.44/1.67  thf('21', plain,
% 1.44/1.67      (((k1_relset_1 @ sk_A @ sk_C_2 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.44/1.67      inference('sup-', [status(thm)], ['19', '20'])).
% 1.44/1.67  thf('22', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.67  thf(d1_funct_2, axiom,
% 1.44/1.67    (![A:$i,B:$i,C:$i]:
% 1.44/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.44/1.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.44/1.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.44/1.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.44/1.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.44/1.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.44/1.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.44/1.67  thf(zf_stmt_1, axiom,
% 1.44/1.67    (![C:$i,B:$i,A:$i]:
% 1.44/1.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.44/1.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.44/1.67  thf('23', plain,
% 1.44/1.67      (![X54 : $i, X55 : $i, X56 : $i]:
% 1.44/1.67         (~ (v1_funct_2 @ X56 @ X54 @ X55)
% 1.44/1.67          | ((X54) = (k1_relset_1 @ X54 @ X55 @ X56))
% 1.44/1.67          | ~ (zip_tseitin_1 @ X56 @ X55 @ X54))),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.44/1.67  thf('24', plain,
% 1.44/1.67      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.44/1.67        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 1.44/1.67      inference('sup-', [status(thm)], ['22', '23'])).
% 1.44/1.67  thf('25', plain,
% 1.44/1.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.67  thf('26', plain,
% 1.44/1.67      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.44/1.67         (((k1_relset_1 @ X37 @ X38 @ X36) = (k1_relat_1 @ X36))
% 1.44/1.67          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 1.44/1.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.44/1.67  thf('27', plain,
% 1.44/1.67      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.44/1.67      inference('sup-', [status(thm)], ['25', '26'])).
% 1.44/1.67  thf('28', plain,
% 1.44/1.67      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.44/1.67        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.44/1.67      inference('demod', [status(thm)], ['24', '27'])).
% 1.44/1.67  thf(zf_stmt_2, axiom,
% 1.44/1.67    (![B:$i,A:$i]:
% 1.44/1.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.44/1.67       ( zip_tseitin_0 @ B @ A ) ))).
% 1.44/1.67  thf('29', plain,
% 1.44/1.67      (![X52 : $i, X53 : $i]:
% 1.44/1.67         ((zip_tseitin_0 @ X52 @ X53) | ((X52) = (k1_xboole_0)))),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.44/1.67  thf('30', plain,
% 1.44/1.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.67  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.44/1.67  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.44/1.67  thf(zf_stmt_5, axiom,
% 1.44/1.67    (![A:$i,B:$i,C:$i]:
% 1.44/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.44/1.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.44/1.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.44/1.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.44/1.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.44/1.67  thf('31', plain,
% 1.44/1.67      (![X57 : $i, X58 : $i, X59 : $i]:
% 1.44/1.67         (~ (zip_tseitin_0 @ X57 @ X58)
% 1.44/1.67          | (zip_tseitin_1 @ X59 @ X57 @ X58)
% 1.44/1.67          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X57))))),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.44/1.67  thf('32', plain,
% 1.44/1.67      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.44/1.67        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.44/1.67      inference('sup-', [status(thm)], ['30', '31'])).
% 1.44/1.67  thf('33', plain,
% 1.44/1.67      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 1.44/1.67      inference('sup-', [status(thm)], ['29', '32'])).
% 1.44/1.67  thf('34', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.67  thf('35', plain,
% 1.44/1.67      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.44/1.67      inference('split', [status(esa)], ['34'])).
% 1.44/1.67  thf(d3_tarski, axiom,
% 1.44/1.67    (![A:$i,B:$i]:
% 1.44/1.67     ( ( r1_tarski @ A @ B ) <=>
% 1.44/1.67       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.44/1.67  thf('36', plain,
% 1.44/1.67      (![X4 : $i, X6 : $i]:
% 1.44/1.67         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.44/1.67      inference('cnf', [status(esa)], [d3_tarski])).
% 1.44/1.67  thf('37', plain,
% 1.44/1.67      (![X4 : $i, X6 : $i]:
% 1.44/1.67         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.44/1.67      inference('cnf', [status(esa)], [d3_tarski])).
% 1.44/1.67  thf('38', plain,
% 1.44/1.67      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.44/1.67      inference('sup-', [status(thm)], ['36', '37'])).
% 1.44/1.67  thf('39', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.44/1.67      inference('simplify', [status(thm)], ['38'])).
% 1.44/1.67  thf(t3_subset, axiom,
% 1.44/1.67    (![A:$i,B:$i]:
% 1.44/1.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.44/1.67  thf('40', plain,
% 1.44/1.67      (![X22 : $i, X24 : $i]:
% 1.44/1.67         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 1.44/1.67      inference('cnf', [status(esa)], [t3_subset])).
% 1.44/1.67  thf('41', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.44/1.67      inference('sup-', [status(thm)], ['39', '40'])).
% 1.44/1.67  thf(t113_zfmisc_1, axiom,
% 1.44/1.67    (![A:$i,B:$i]:
% 1.44/1.67     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.44/1.67       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.44/1.67  thf('42', plain,
% 1.44/1.67      (![X12 : $i, X13 : $i]:
% 1.44/1.67         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 1.44/1.67          | ((X12) != (k1_xboole_0)))),
% 1.44/1.67      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.44/1.67  thf('43', plain,
% 1.44/1.67      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 1.44/1.67      inference('simplify', [status(thm)], ['42'])).
% 1.44/1.67  thf(cc1_partfun1, axiom,
% 1.44/1.67    (![A:$i,B:$i]:
% 1.44/1.67     ( ( v1_xboole_0 @ A ) =>
% 1.44/1.67       ( ![C:$i]:
% 1.44/1.67         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.44/1.67           ( v1_partfun1 @ C @ A ) ) ) ))).
% 1.44/1.67  thf('44', plain,
% 1.44/1.67      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.44/1.67         (~ (v1_xboole_0 @ X49)
% 1.44/1.67          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X51)))
% 1.44/1.67          | (v1_partfun1 @ X50 @ X49))),
% 1.44/1.67      inference('cnf', [status(esa)], [cc1_partfun1])).
% 1.44/1.67  thf('45', plain,
% 1.44/1.67      (![X1 : $i]:
% 1.44/1.67         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.44/1.67          | (v1_partfun1 @ X1 @ k1_xboole_0)
% 1.44/1.67          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.44/1.67      inference('sup-', [status(thm)], ['43', '44'])).
% 1.44/1.67  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.44/1.67  thf('46', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 1.44/1.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.44/1.67  thf(d1_xboole_0, axiom,
% 1.44/1.67    (![A:$i]:
% 1.44/1.67     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.44/1.67  thf('47', plain,
% 1.44/1.67      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.44/1.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.44/1.67  thf(t7_ordinal1, axiom,
% 1.44/1.67    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.44/1.67  thf('48', plain,
% 1.44/1.67      (![X28 : $i, X29 : $i]:
% 1.44/1.67         (~ (r2_hidden @ X28 @ X29) | ~ (r1_tarski @ X29 @ X28))),
% 1.44/1.67      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.44/1.67  thf('49', plain,
% 1.44/1.67      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 1.44/1.67      inference('sup-', [status(thm)], ['47', '48'])).
% 1.44/1.67  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.44/1.67      inference('sup-', [status(thm)], ['46', '49'])).
% 1.44/1.67  thf('51', plain,
% 1.44/1.67      (![X1 : $i]:
% 1.44/1.67         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.44/1.67          | (v1_partfun1 @ X1 @ k1_xboole_0))),
% 1.44/1.67      inference('demod', [status(thm)], ['45', '50'])).
% 1.44/1.67  thf('52', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 1.44/1.67      inference('sup-', [status(thm)], ['41', '51'])).
% 1.44/1.67  thf('53', plain,
% 1.44/1.67      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.44/1.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.44/1.67  thf('54', plain,
% 1.44/1.67      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 1.44/1.67      inference('simplify', [status(thm)], ['42'])).
% 1.44/1.67  thf('55', plain,
% 1.44/1.67      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('split', [status(esa)], ['34'])).
% 1.44/1.67  thf('56', plain,
% 1.44/1.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.67  thf('57', plain,
% 1.44/1.67      (((m1_subset_1 @ sk_D @ 
% 1.44/1.67         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.44/1.67         <= ((((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('sup+', [status(thm)], ['55', '56'])).
% 1.44/1.67  thf('58', plain,
% 1.44/1.67      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.44/1.67         <= ((((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('sup+', [status(thm)], ['54', '57'])).
% 1.44/1.67  thf('59', plain,
% 1.44/1.67      (![X22 : $i, X23 : $i]:
% 1.44/1.67         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 1.44/1.67      inference('cnf', [status(esa)], [t3_subset])).
% 1.44/1.67  thf('60', plain,
% 1.44/1.67      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('sup-', [status(thm)], ['58', '59'])).
% 1.44/1.67  thf('61', plain,
% 1.44/1.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.44/1.67         (~ (r2_hidden @ X3 @ X4)
% 1.44/1.67          | (r2_hidden @ X3 @ X5)
% 1.44/1.67          | ~ (r1_tarski @ X4 @ X5))),
% 1.44/1.67      inference('cnf', [status(esa)], [d3_tarski])).
% 1.44/1.67  thf('62', plain,
% 1.44/1.67      ((![X0 : $i]:
% 1.44/1.67          ((r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 1.44/1.67         <= ((((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('sup-', [status(thm)], ['60', '61'])).
% 1.44/1.67  thf('63', plain,
% 1.44/1.67      ((((v1_xboole_0 @ sk_D) | (r2_hidden @ (sk_B @ sk_D) @ k1_xboole_0)))
% 1.44/1.67         <= ((((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('sup-', [status(thm)], ['53', '62'])).
% 1.44/1.67  thf('64', plain,
% 1.44/1.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.44/1.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.44/1.67  thf('65', plain,
% 1.44/1.67      ((((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.44/1.67         <= ((((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('sup-', [status(thm)], ['63', '64'])).
% 1.44/1.67  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.44/1.67      inference('sup-', [status(thm)], ['46', '49'])).
% 1.44/1.67  thf('67', plain, (((v1_xboole_0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('demod', [status(thm)], ['65', '66'])).
% 1.44/1.67  thf(l13_xboole_0, axiom,
% 1.44/1.67    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.44/1.67  thf('68', plain,
% 1.44/1.67      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.44/1.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.44/1.67  thf('69', plain,
% 1.44/1.67      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('sup-', [status(thm)], ['67', '68'])).
% 1.44/1.67  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.67  thf('71', plain,
% 1.44/1.67      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('sup+', [status(thm)], ['69', '70'])).
% 1.44/1.67  thf('72', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 1.44/1.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.44/1.67  thf('73', plain,
% 1.44/1.67      (![X22 : $i, X24 : $i]:
% 1.44/1.67         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 1.44/1.67      inference('cnf', [status(esa)], [t3_subset])).
% 1.44/1.67  thf('74', plain,
% 1.44/1.67      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.44/1.67      inference('sup-', [status(thm)], ['72', '73'])).
% 1.44/1.67  thf(cc1_funct_2, axiom,
% 1.44/1.67    (![A:$i,B:$i,C:$i]:
% 1.44/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.44/1.67       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 1.44/1.67         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 1.44/1.67  thf('75', plain,
% 1.44/1.67      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.44/1.67         (~ (v1_funct_1 @ X46)
% 1.44/1.67          | ~ (v1_partfun1 @ X46 @ X47)
% 1.44/1.67          | (v1_funct_2 @ X46 @ X47 @ X48)
% 1.44/1.67          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 1.44/1.67      inference('cnf', [status(esa)], [cc1_funct_2])).
% 1.44/1.67  thf('76', plain,
% 1.44/1.67      (![X0 : $i, X1 : $i]:
% 1.44/1.67         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 1.44/1.67          | ~ (v1_partfun1 @ k1_xboole_0 @ X1)
% 1.44/1.67          | ~ (v1_funct_1 @ k1_xboole_0))),
% 1.44/1.67      inference('sup-', [status(thm)], ['74', '75'])).
% 1.44/1.67  thf('77', plain,
% 1.44/1.67      ((![X0 : $i, X1 : $i]:
% 1.44/1.67          (~ (v1_partfun1 @ k1_xboole_0 @ X0)
% 1.44/1.67           | (v1_funct_2 @ k1_xboole_0 @ X0 @ X1)))
% 1.44/1.67         <= ((((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('sup-', [status(thm)], ['71', '76'])).
% 1.44/1.67  thf('78', plain,
% 1.44/1.67      ((![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))
% 1.44/1.67         <= ((((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('sup-', [status(thm)], ['52', '77'])).
% 1.44/1.67  thf('79', plain,
% 1.44/1.67      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('sup-', [status(thm)], ['67', '68'])).
% 1.44/1.67  thf('80', plain,
% 1.44/1.67      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('split', [status(esa)], ['34'])).
% 1.44/1.67  thf('81', plain,
% 1.44/1.67      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_2))
% 1.44/1.67         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_2)))),
% 1.44/1.67      inference('split', [status(esa)], ['0'])).
% 1.44/1.67  thf('82', plain,
% 1.44/1.67      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_2))
% 1.44/1.67         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_2)) & 
% 1.44/1.67             (((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('sup-', [status(thm)], ['80', '81'])).
% 1.44/1.67  thf('83', plain,
% 1.44/1.67      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2))
% 1.44/1.67         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_2)) & 
% 1.44/1.67             (((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('sup-', [status(thm)], ['79', '82'])).
% 1.44/1.67  thf('84', plain,
% 1.44/1.67      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_2)) | ~ (((sk_A) = (k1_xboole_0)))),
% 1.44/1.67      inference('sup-', [status(thm)], ['78', '83'])).
% 1.44/1.67  thf('85', plain,
% 1.44/1.67      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.44/1.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.44/1.67  thf('86', plain,
% 1.44/1.67      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 1.44/1.67      inference('simplify', [status(thm)], ['42'])).
% 1.44/1.67  thf('87', plain,
% 1.44/1.67      (![X0 : $i, X1 : $i]:
% 1.44/1.67         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.44/1.67      inference('sup+', [status(thm)], ['85', '86'])).
% 1.44/1.67  thf('88', plain,
% 1.44/1.67      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('split', [status(esa)], ['34'])).
% 1.44/1.67  thf('89', plain,
% 1.44/1.67      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2))))
% 1.44/1.67         <= (~
% 1.44/1.67             ((m1_subset_1 @ sk_D @ 
% 1.44/1.67               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2)))))),
% 1.44/1.67      inference('split', [status(esa)], ['0'])).
% 1.44/1.67  thf('90', plain,
% 1.44/1.67      ((~ (m1_subset_1 @ sk_D @ 
% 1.44/1.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_2))))
% 1.44/1.67         <= (~
% 1.44/1.67             ((m1_subset_1 @ sk_D @ 
% 1.44/1.67               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2)))) & 
% 1.44/1.67             (((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('sup-', [status(thm)], ['88', '89'])).
% 1.44/1.67  thf('91', plain,
% 1.44/1.67      (((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.44/1.67         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.44/1.67         <= (~
% 1.44/1.67             ((m1_subset_1 @ sk_D @ 
% 1.44/1.67               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2)))) & 
% 1.44/1.67             (((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('sup-', [status(thm)], ['87', '90'])).
% 1.44/1.67  thf('92', plain,
% 1.44/1.67      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.44/1.67         <= ((((sk_A) = (k1_xboole_0))))),
% 1.44/1.67      inference('sup+', [status(thm)], ['54', '57'])).
% 1.44/1.67  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.44/1.67      inference('sup-', [status(thm)], ['46', '49'])).
% 1.44/1.67  thf('94', plain,
% 1.44/1.67      (~ (((sk_A) = (k1_xboole_0))) | 
% 1.44/1.67       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2))))),
% 1.44/1.67      inference('demod', [status(thm)], ['91', '92', '93'])).
% 1.44/1.67  thf('95', plain,
% 1.44/1.67      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2)))) | 
% 1.44/1.67       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_2)) | ~ ((v1_funct_1 @ sk_D))),
% 1.44/1.67      inference('split', [status(esa)], ['0'])).
% 1.44/1.67  thf('96', plain,
% 1.44/1.67      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.44/1.67      inference('split', [status(esa)], ['34'])).
% 1.44/1.67  thf('97', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 1.44/1.67      inference('sat_resolution*', [status(thm)], ['4', '84', '94', '95', '96'])).
% 1.44/1.67  thf('98', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.44/1.67      inference('simpl_trail', [status(thm)], ['35', '97'])).
% 1.44/1.67  thf('99', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 1.44/1.67      inference('simplify_reflect-', [status(thm)], ['33', '98'])).
% 1.44/1.67  thf('100', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.44/1.67      inference('demod', [status(thm)], ['28', '99'])).
% 1.44/1.67  thf('101', plain, (((k1_relset_1 @ sk_A @ sk_C_2 @ sk_D) = (sk_A))),
% 1.44/1.67      inference('demod', [status(thm)], ['21', '100'])).
% 1.44/1.67  thf('102', plain,
% 1.44/1.67      (![X54 : $i, X55 : $i, X56 : $i]:
% 1.44/1.67         (((X54) != (k1_relset_1 @ X54 @ X55 @ X56))
% 1.44/1.67          | (v1_funct_2 @ X56 @ X54 @ X55)
% 1.44/1.67          | ~ (zip_tseitin_1 @ X56 @ X55 @ X54))),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.44/1.67  thf('103', plain,
% 1.44/1.67      ((((sk_A) != (sk_A))
% 1.44/1.67        | ~ (zip_tseitin_1 @ sk_D @ sk_C_2 @ sk_A)
% 1.44/1.67        | (v1_funct_2 @ sk_D @ sk_A @ sk_C_2))),
% 1.44/1.67      inference('sup-', [status(thm)], ['101', '102'])).
% 1.44/1.67  thf('104', plain,
% 1.44/1.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2)))),
% 1.44/1.67      inference('sup-', [status(thm)], ['9', '12'])).
% 1.44/1.67  thf('105', plain,
% 1.44/1.67      (![X57 : $i, X58 : $i, X59 : $i]:
% 1.44/1.67         (~ (zip_tseitin_0 @ X57 @ X58)
% 1.44/1.67          | (zip_tseitin_1 @ X59 @ X57 @ X58)
% 1.44/1.67          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X57))))),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.44/1.67  thf('106', plain,
% 1.44/1.67      (((zip_tseitin_1 @ sk_D @ sk_C_2 @ sk_A)
% 1.44/1.67        | ~ (zip_tseitin_0 @ sk_C_2 @ sk_A))),
% 1.44/1.67      inference('sup-', [status(thm)], ['104', '105'])).
% 1.44/1.67  thf('107', plain,
% 1.44/1.67      (![X52 : $i, X53 : $i]:
% 1.44/1.67         ((zip_tseitin_0 @ X52 @ X53) | ((X52) = (k1_xboole_0)))),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.44/1.67  thf('108', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.44/1.67      inference('sup-', [status(thm)], ['46', '49'])).
% 1.44/1.67  thf('109', plain,
% 1.44/1.67      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.44/1.67      inference('sup+', [status(thm)], ['107', '108'])).
% 1.44/1.67  thf('110', plain,
% 1.44/1.67      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ sk_C_2)),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.67  thf('111', plain,
% 1.44/1.67      (![X22 : $i, X24 : $i]:
% 1.44/1.67         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 1.44/1.67      inference('cnf', [status(esa)], [t3_subset])).
% 1.44/1.67  thf('112', plain,
% 1.44/1.67      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ 
% 1.44/1.67        (k1_zfmisc_1 @ sk_C_2))),
% 1.44/1.67      inference('sup-', [status(thm)], ['110', '111'])).
% 1.44/1.67  thf(cc1_subset_1, axiom,
% 1.44/1.67    (![A:$i]:
% 1.44/1.67     ( ( v1_xboole_0 @ A ) =>
% 1.44/1.67       ( ![B:$i]:
% 1.44/1.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 1.44/1.67  thf('113', plain,
% 1.44/1.67      (![X20 : $i, X21 : $i]:
% 1.44/1.67         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 1.44/1.67          | (v1_xboole_0 @ X20)
% 1.44/1.67          | ~ (v1_xboole_0 @ X21))),
% 1.44/1.67      inference('cnf', [status(esa)], [cc1_subset_1])).
% 1.44/1.67  thf('114', plain,
% 1.44/1.67      ((~ (v1_xboole_0 @ sk_C_2)
% 1.44/1.67        | (v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 1.44/1.67      inference('sup-', [status(thm)], ['112', '113'])).
% 1.44/1.67  thf('115', plain,
% 1.44/1.67      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.44/1.67      inference('sup-', [status(thm)], ['6', '7'])).
% 1.44/1.67  thf('116', plain,
% 1.44/1.67      ((~ (v1_xboole_0 @ sk_C_2) | (v1_xboole_0 @ (k2_relat_1 @ sk_D)))),
% 1.44/1.67      inference('demod', [status(thm)], ['114', '115'])).
% 1.44/1.67  thf('117', plain,
% 1.44/1.67      (![X0 : $i]:
% 1.44/1.67         ((zip_tseitin_0 @ sk_C_2 @ X0) | (v1_xboole_0 @ (k2_relat_1 @ sk_D)))),
% 1.44/1.67      inference('sup-', [status(thm)], ['109', '116'])).
% 1.44/1.67  thf('118', plain,
% 1.44/1.67      (![X12 : $i, X13 : $i]:
% 1.44/1.67         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 1.44/1.67          | ((X13) != (k1_xboole_0)))),
% 1.44/1.67      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.44/1.67  thf('119', plain,
% 1.44/1.67      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 1.44/1.67      inference('simplify', [status(thm)], ['118'])).
% 1.44/1.67  thf('120', plain,
% 1.44/1.67      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.44/1.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.44/1.67  thf('121', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 1.44/1.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.44/1.67  thf('122', plain,
% 1.44/1.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.44/1.67      inference('sup+', [status(thm)], ['120', '121'])).
% 1.44/1.67  thf(t118_zfmisc_1, axiom,
% 1.44/1.67    (![A:$i,B:$i,C:$i]:
% 1.44/1.67     ( ( r1_tarski @ A @ B ) =>
% 1.44/1.67       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 1.44/1.67         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 1.44/1.67  thf('123', plain,
% 1.44/1.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.44/1.67         (~ (r1_tarski @ X14 @ X15)
% 1.44/1.67          | (r1_tarski @ (k2_zfmisc_1 @ X16 @ X14) @ (k2_zfmisc_1 @ X16 @ X15)))),
% 1.44/1.67      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 1.44/1.67  thf('124', plain,
% 1.44/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.67         (~ (v1_xboole_0 @ X1)
% 1.44/1.67          | (r1_tarski @ (k2_zfmisc_1 @ X2 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 1.44/1.67      inference('sup-', [status(thm)], ['122', '123'])).
% 1.44/1.67  thf('125', plain,
% 1.44/1.67      (![X0 : $i, X1 : $i]:
% 1.44/1.67         ((r1_tarski @ (k2_zfmisc_1 @ X0 @ X1) @ k1_xboole_0)
% 1.44/1.67          | ~ (v1_xboole_0 @ X1))),
% 1.44/1.67      inference('sup+', [status(thm)], ['119', '124'])).
% 1.44/1.67  thf('126', plain,
% 1.44/1.67      (![X22 : $i, X24 : $i]:
% 1.44/1.67         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 1.44/1.67      inference('cnf', [status(esa)], [t3_subset])).
% 1.44/1.67  thf('127', plain,
% 1.44/1.67      (![X0 : $i, X1 : $i]:
% 1.44/1.67         (~ (v1_xboole_0 @ X0)
% 1.44/1.67          | (m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 1.44/1.67             (k1_zfmisc_1 @ k1_xboole_0)))),
% 1.44/1.67      inference('sup-', [status(thm)], ['125', '126'])).
% 1.44/1.67  thf('128', plain,
% 1.44/1.67      (![X20 : $i, X21 : $i]:
% 1.44/1.67         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 1.44/1.67          | (v1_xboole_0 @ X20)
% 1.44/1.67          | ~ (v1_xboole_0 @ X21))),
% 1.44/1.67      inference('cnf', [status(esa)], [cc1_subset_1])).
% 1.44/1.67  thf('129', plain,
% 1.44/1.67      (![X0 : $i, X1 : $i]:
% 1.44/1.67         (~ (v1_xboole_0 @ X0)
% 1.44/1.67          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.44/1.67          | (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.44/1.67      inference('sup-', [status(thm)], ['127', '128'])).
% 1.44/1.67  thf('130', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.44/1.67      inference('sup-', [status(thm)], ['46', '49'])).
% 1.44/1.67  thf('131', plain,
% 1.44/1.67      (![X0 : $i, X1 : $i]:
% 1.44/1.67         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.44/1.67      inference('demod', [status(thm)], ['129', '130'])).
% 1.44/1.67  thf('132', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.44/1.67      inference('demod', [status(thm)], ['28', '99'])).
% 1.44/1.67  thf(t21_relat_1, axiom,
% 1.44/1.67    (![A:$i]:
% 1.44/1.67     ( ( v1_relat_1 @ A ) =>
% 1.44/1.67       ( r1_tarski @
% 1.44/1.67         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.44/1.67  thf('133', plain,
% 1.44/1.67      (![X27 : $i]:
% 1.44/1.67         ((r1_tarski @ X27 @ 
% 1.44/1.67           (k2_zfmisc_1 @ (k1_relat_1 @ X27) @ (k2_relat_1 @ X27)))
% 1.44/1.67          | ~ (v1_relat_1 @ X27))),
% 1.44/1.67      inference('cnf', [status(esa)], [t21_relat_1])).
% 1.44/1.67  thf('134', plain,
% 1.44/1.67      (((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_D)))
% 1.44/1.67        | ~ (v1_relat_1 @ sk_D))),
% 1.44/1.67      inference('sup+', [status(thm)], ['132', '133'])).
% 1.44/1.67  thf('135', plain,
% 1.44/1.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.67  thf(cc1_relset_1, axiom,
% 1.44/1.67    (![A:$i,B:$i,C:$i]:
% 1.44/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.44/1.67       ( v1_relat_1 @ C ) ))).
% 1.44/1.67  thf('136', plain,
% 1.44/1.67      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.44/1.67         ((v1_relat_1 @ X30)
% 1.44/1.67          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.44/1.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.44/1.67  thf('137', plain, ((v1_relat_1 @ sk_D)),
% 1.44/1.67      inference('sup-', [status(thm)], ['135', '136'])).
% 1.44/1.67  thf('138', plain,
% 1.44/1.67      ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_D)))),
% 1.44/1.67      inference('demod', [status(thm)], ['134', '137'])).
% 1.44/1.67  thf('139', plain,
% 1.44/1.67      (![X22 : $i, X24 : $i]:
% 1.44/1.67         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 1.44/1.67      inference('cnf', [status(esa)], [t3_subset])).
% 1.44/1.67  thf('140', plain,
% 1.44/1.67      ((m1_subset_1 @ sk_D @ 
% 1.44/1.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_D))))),
% 1.44/1.67      inference('sup-', [status(thm)], ['138', '139'])).
% 1.44/1.67  thf('141', plain,
% 1.44/1.67      (![X20 : $i, X21 : $i]:
% 1.44/1.67         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 1.44/1.67          | (v1_xboole_0 @ X20)
% 1.44/1.67          | ~ (v1_xboole_0 @ X21))),
% 1.44/1.67      inference('cnf', [status(esa)], [cc1_subset_1])).
% 1.44/1.67  thf('142', plain,
% 1.44/1.67      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_D)))
% 1.44/1.67        | (v1_xboole_0 @ sk_D))),
% 1.44/1.67      inference('sup-', [status(thm)], ['140', '141'])).
% 1.44/1.67  thf('143', plain,
% 1.44/1.67      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_D)) | (v1_xboole_0 @ sk_D))),
% 1.44/1.67      inference('sup-', [status(thm)], ['131', '142'])).
% 1.44/1.67  thf('144', plain,
% 1.44/1.67      (![X0 : $i]: ((zip_tseitin_0 @ sk_C_2 @ X0) | (v1_xboole_0 @ sk_D))),
% 1.44/1.67      inference('sup-', [status(thm)], ['117', '143'])).
% 1.44/1.67  thf('145', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.44/1.67      inference('demod', [status(thm)], ['28', '99'])).
% 1.44/1.67  thf('146', plain,
% 1.44/1.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.44/1.67      inference('sup+', [status(thm)], ['120', '121'])).
% 1.44/1.67  thf('147', plain,
% 1.44/1.67      (![X22 : $i, X24 : $i]:
% 1.44/1.67         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 1.44/1.67      inference('cnf', [status(esa)], [t3_subset])).
% 1.44/1.67  thf('148', plain,
% 1.44/1.67      (![X0 : $i, X1 : $i]:
% 1.44/1.67         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.44/1.67      inference('sup-', [status(thm)], ['146', '147'])).
% 1.44/1.67  thf(cc2_relset_1, axiom,
% 1.44/1.67    (![A:$i,B:$i,C:$i]:
% 1.44/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.44/1.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.44/1.67  thf('149', plain,
% 1.44/1.67      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.44/1.67         ((v4_relat_1 @ X33 @ X34)
% 1.44/1.67          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 1.44/1.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.44/1.67  thf('150', plain,
% 1.44/1.67      (![X1 : $i, X2 : $i]: (~ (v1_xboole_0 @ X2) | (v4_relat_1 @ X2 @ X1))),
% 1.44/1.67      inference('sup-', [status(thm)], ['148', '149'])).
% 1.44/1.67  thf(d18_relat_1, axiom,
% 1.44/1.67    (![A:$i,B:$i]:
% 1.44/1.67     ( ( v1_relat_1 @ B ) =>
% 1.44/1.67       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.44/1.67  thf('151', plain,
% 1.44/1.67      (![X25 : $i, X26 : $i]:
% 1.44/1.67         (~ (v4_relat_1 @ X25 @ X26)
% 1.44/1.67          | (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 1.44/1.67          | ~ (v1_relat_1 @ X25))),
% 1.44/1.67      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.44/1.67  thf('152', plain,
% 1.44/1.67      (![X0 : $i, X1 : $i]:
% 1.44/1.67         (~ (v1_xboole_0 @ X1)
% 1.44/1.67          | ~ (v1_relat_1 @ X1)
% 1.44/1.67          | (r1_tarski @ (k1_relat_1 @ X1) @ X0))),
% 1.44/1.67      inference('sup-', [status(thm)], ['150', '151'])).
% 1.44/1.67  thf('153', plain,
% 1.44/1.67      (![X0 : $i, X1 : $i]:
% 1.44/1.67         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.44/1.67      inference('sup-', [status(thm)], ['146', '147'])).
% 1.44/1.67  thf('154', plain,
% 1.44/1.67      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.44/1.67         ((v1_relat_1 @ X30)
% 1.44/1.67          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.44/1.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.44/1.67  thf('155', plain, (![X2 : $i]: (~ (v1_xboole_0 @ X2) | (v1_relat_1 @ X2))),
% 1.44/1.67      inference('sup-', [status(thm)], ['153', '154'])).
% 1.44/1.67  thf('156', plain,
% 1.44/1.67      (![X0 : $i, X1 : $i]:
% 1.44/1.67         ((r1_tarski @ (k1_relat_1 @ X1) @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.44/1.67      inference('clc', [status(thm)], ['152', '155'])).
% 1.44/1.67  thf('157', plain,
% 1.44/1.67      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 1.44/1.67      inference('sup-', [status(thm)], ['47', '48'])).
% 1.44/1.67  thf('158', plain,
% 1.44/1.67      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 1.44/1.67      inference('sup-', [status(thm)], ['156', '157'])).
% 1.44/1.67  thf('159', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_D))),
% 1.44/1.67      inference('sup+', [status(thm)], ['145', '158'])).
% 1.44/1.67  thf('160', plain,
% 1.44/1.67      (![X0 : $i]: ((zip_tseitin_0 @ sk_C_2 @ X0) | (v1_xboole_0 @ sk_A))),
% 1.44/1.67      inference('sup-', [status(thm)], ['144', '159'])).
% 1.44/1.67  thf('161', plain,
% 1.44/1.67      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.44/1.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.44/1.67  thf('162', plain,
% 1.44/1.67      (![X52 : $i, X53 : $i]:
% 1.44/1.67         ((zip_tseitin_0 @ X52 @ X53) | ((X53) != (k1_xboole_0)))),
% 1.44/1.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.44/1.67  thf('163', plain, (![X52 : $i]: (zip_tseitin_0 @ X52 @ k1_xboole_0)),
% 1.44/1.67      inference('simplify', [status(thm)], ['162'])).
% 1.44/1.67  thf('164', plain,
% 1.44/1.67      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 1.44/1.67      inference('sup+', [status(thm)], ['161', '163'])).
% 1.44/1.67  thf('165', plain,
% 1.44/1.67      (![X0 : $i, X1 : $i]:
% 1.44/1.67         ((zip_tseitin_0 @ sk_C_2 @ X1) | (zip_tseitin_0 @ X0 @ sk_A))),
% 1.44/1.67      inference('sup-', [status(thm)], ['160', '164'])).
% 1.44/1.67  thf('166', plain, ((zip_tseitin_0 @ sk_C_2 @ sk_A)),
% 1.44/1.67      inference('eq_fact', [status(thm)], ['165'])).
% 1.44/1.67  thf('167', plain, ((zip_tseitin_1 @ sk_D @ sk_C_2 @ sk_A)),
% 1.44/1.67      inference('demod', [status(thm)], ['106', '166'])).
% 1.44/1.67  thf('168', plain,
% 1.44/1.67      ((((sk_A) != (sk_A)) | (v1_funct_2 @ sk_D @ sk_A @ sk_C_2))),
% 1.44/1.67      inference('demod', [status(thm)], ['103', '167'])).
% 1.44/1.67  thf('169', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_C_2)),
% 1.44/1.67      inference('simplify', [status(thm)], ['168'])).
% 1.44/1.67  thf('170', plain, ($false), inference('demod', [status(thm)], ['18', '169'])).
% 1.44/1.67  
% 1.44/1.67  % SZS output end Refutation
% 1.44/1.67  
% 1.44/1.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
