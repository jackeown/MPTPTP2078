%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.leThiyNrFR

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:11 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 460 expanded)
%              Number of leaves         :   37 ( 139 expanded)
%              Depth                    :   22
%              Number of atoms          : 1063 (6406 expanded)
%              Number of equality atoms :   95 ( 502 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
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
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v5_relat_1 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['10','15'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','18'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X44 ) @ X45 )
      | ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X44 ) @ X45 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
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
      ( ( zip_tseitin_5 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('25',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_5 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,
    ( ~ ( zip_tseitin_5 @ sk_D @ sk_B @ sk_A )
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( zip_tseitin_5 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_4 @ B @ A ) ) )).

thf('31',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_4 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_4 @ B @ A )
         => ( zip_tseitin_5 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_4 @ X41 @ X42 )
      | ( zip_tseitin_5 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('34',plain,
    ( ( zip_tseitin_5 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_4 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_5 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('39',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_5 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('42',plain,
    ( ( ~ ( zip_tseitin_5 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('44',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('50',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( ~ ( zip_tseitin_5 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('55',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_4 @ X41 @ X42 )
      | ( zip_tseitin_5 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,
    ( ( ( zip_tseitin_5 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_4 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_4 @ X36 @ X37 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('58',plain,(
    ! [X36: $i] :
      ( zip_tseitin_4 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( zip_tseitin_5 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','58'])).

thf('60',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','59'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('61',plain,(
    ! [X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('62',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('64',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('69',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('70',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('72',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_5 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_5 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_5 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X36: $i] :
      ( zip_tseitin_4 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('78',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('79',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_4 @ X41 @ X42 )
      | ( zip_tseitin_5 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_5 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_4 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( zip_tseitin_5 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['76','81'])).

thf('83',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68','82'])).

thf('84',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('85',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('86',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('90',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('92',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('93',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','83','90','91','92'])).

thf('94',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['37','93'])).

thf('95',plain,(
    zip_tseitin_5 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['35','94'])).

thf('96',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['30','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','22','23','96'])).

thf('98',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('99',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['4','99','100'])).

thf('102',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','101'])).

thf('103',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','18'])).

thf('104',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X44 ) @ X45 )
      | ( v1_funct_2 @ X44 @ ( k1_relat_1 @ X44 ) @ X45 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('107',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['30','95'])).

thf('109',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,(
    $false ),
    inference(demod,[status(thm)],['102','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.leThiyNrFR
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 304 iterations in 0.125s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.59  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $i > $o).
% 0.39/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.59  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.39/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.59  thf(t9_funct_2, conjecture,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.59       ( ( r1_tarski @ B @ C ) =>
% 0.39/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.39/0.59           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.39/0.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.59        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.59            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.59          ( ( r1_tarski @ B @ C ) =>
% 0.39/0.59            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.39/0.59              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.39/0.59                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      ((~ (v1_funct_1 @ sk_D)
% 0.39/0.59        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 0.39/0.59        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.39/0.59         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.39/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.59  thf('5', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(cc2_relset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.59  thf('7', plain,
% 0.39/0.59      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.39/0.59         ((v5_relat_1 @ X30 @ X32)
% 0.39/0.59          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.39/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.59  thf('8', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.39/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.59  thf(d19_relat_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( v1_relat_1 @ B ) =>
% 0.39/0.59       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i]:
% 0.39/0.59         (~ (v5_relat_1 @ X14 @ X15)
% 0.39/0.59          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.39/0.59          | ~ (v1_relat_1 @ X14))),
% 0.39/0.59      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.59  thf('11', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(cc2_relat_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( v1_relat_1 @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      (![X12 : $i, X13 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.39/0.59          | (v1_relat_1 @ X12)
% 0.39/0.59          | ~ (v1_relat_1 @ X13))),
% 0.39/0.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.39/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.39/0.59  thf(fc6_relat_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.39/0.59      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.39/0.59  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.59      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.59  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.39/0.59      inference('demod', [status(thm)], ['10', '15'])).
% 0.39/0.59  thf(t1_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.39/0.59       ( r1_tarski @ A @ C ) ))).
% 0.39/0.59  thf('17', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (~ (r1_tarski @ X0 @ X1)
% 0.39/0.59          | ~ (r1_tarski @ X1 @ X2)
% 0.39/0.59          | (r1_tarski @ X0 @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.59  thf('19', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 0.39/0.59      inference('sup-', [status(thm)], ['5', '18'])).
% 0.39/0.59  thf(t4_funct_2, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.59       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.39/0.59         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.39/0.59           ( m1_subset_1 @
% 0.39/0.59             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      (![X44 : $i, X45 : $i]:
% 0.39/0.59         (~ (r1_tarski @ (k2_relat_1 @ X44) @ X45)
% 0.39/0.59          | (m1_subset_1 @ X44 @ 
% 0.39/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X44) @ X45)))
% 0.39/0.59          | ~ (v1_funct_1 @ X44)
% 0.39/0.59          | ~ (v1_relat_1 @ X44))),
% 0.39/0.59      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ sk_D)
% 0.39/0.59        | ~ (v1_funct_1 @ sk_D)
% 0.39/0.59        | (m1_subset_1 @ sk_D @ 
% 0.39/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C_1))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.59  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.59      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.59  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(d1_funct_2, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.39/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.39/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_1, axiom,
% 0.39/0.59    (![C:$i,B:$i,A:$i]:
% 0.39/0.59     ( ( zip_tseitin_5 @ C @ B @ A ) =>
% 0.39/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.39/0.59         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.39/0.59          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 0.39/0.59          | ~ (zip_tseitin_5 @ X40 @ X39 @ X38))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      ((~ (zip_tseitin_5 @ sk_D @ sk_B @ sk_A)
% 0.39/0.59        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.59  thf('28', plain,
% 0.39/0.59      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.39/0.59         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 0.39/0.59          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.39/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.39/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      ((~ (zip_tseitin_5 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.39/0.59      inference('demod', [status(thm)], ['26', '29'])).
% 0.39/0.59  thf(zf_stmt_2, axiom,
% 0.39/0.59    (![B:$i,A:$i]:
% 0.39/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.59       ( zip_tseitin_4 @ B @ A ) ))).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      (![X36 : $i, X37 : $i]:
% 0.39/0.59         ((zip_tseitin_4 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(zf_stmt_3, type, zip_tseitin_5 : $i > $i > $i > $o).
% 0.39/0.59  thf(zf_stmt_4, type, zip_tseitin_4 : $i > $i > $o).
% 0.39/0.59  thf(zf_stmt_5, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( ( ( zip_tseitin_4 @ B @ A ) => ( zip_tseitin_5 @ C @ B @ A ) ) & 
% 0.39/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.39/0.59  thf('33', plain,
% 0.39/0.59      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.39/0.59         (~ (zip_tseitin_4 @ X41 @ X42)
% 0.39/0.59          | (zip_tseitin_5 @ X43 @ X41 @ X42)
% 0.39/0.59          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (((zip_tseitin_5 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_4 @ sk_B @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_5 @ sk_D @ sk_B @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['31', '34'])).
% 0.39/0.59  thf('36', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('37', plain,
% 0.39/0.59      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.39/0.59      inference('split', [status(esa)], ['36'])).
% 0.39/0.59  thf('38', plain,
% 0.39/0.59      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('split', [status(esa)], ['36'])).
% 0.39/0.59  thf('39', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('40', plain,
% 0.39/0.59      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.39/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('sup+', [status(thm)], ['38', '39'])).
% 0.39/0.59  thf('41', plain,
% 0.39/0.59      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.39/0.59         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.39/0.59          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 0.39/0.59          | ~ (zip_tseitin_5 @ X40 @ X39 @ X38))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.59  thf('42', plain,
% 0.39/0.59      (((~ (zip_tseitin_5 @ sk_D @ sk_B @ k1_xboole_0)
% 0.39/0.59         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 0.39/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.59  thf(t113_zfmisc_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.59  thf('43', plain,
% 0.39/0.59      (![X5 : $i, X6 : $i]:
% 0.39/0.59         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.59  thf('44', plain,
% 0.39/0.59      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.39/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.39/0.59  thf('45', plain,
% 0.39/0.59      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('split', [status(esa)], ['36'])).
% 0.39/0.59  thf('46', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('47', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_D @ 
% 0.39/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.39/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('sup+', [status(thm)], ['45', '46'])).
% 0.39/0.59  thf('48', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.39/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('sup+', [status(thm)], ['44', '47'])).
% 0.39/0.59  thf('49', plain,
% 0.39/0.59      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.39/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.39/0.59  thf('50', plain,
% 0.39/0.59      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.39/0.59         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 0.39/0.59          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.39/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.59  thf('51', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.39/0.59          | ((k1_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k1_relat_1 @ X1)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['49', '50'])).
% 0.39/0.59  thf('52', plain,
% 0.39/0.59      ((![X0 : $i]:
% 0.39/0.59          ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.39/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['48', '51'])).
% 0.39/0.59  thf('53', plain,
% 0.39/0.59      (((~ (zip_tseitin_5 @ sk_D @ sk_B @ k1_xboole_0)
% 0.39/0.59         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 0.39/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('demod', [status(thm)], ['42', '52'])).
% 0.39/0.59  thf('54', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_D @ 
% 0.39/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.39/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('sup+', [status(thm)], ['45', '46'])).
% 0.39/0.59  thf('55', plain,
% 0.39/0.59      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.39/0.59         (~ (zip_tseitin_4 @ X41 @ X42)
% 0.39/0.59          | (zip_tseitin_5 @ X43 @ X41 @ X42)
% 0.39/0.59          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.59  thf('56', plain,
% 0.39/0.59      ((((zip_tseitin_5 @ sk_D @ sk_B @ k1_xboole_0)
% 0.39/0.59         | ~ (zip_tseitin_4 @ sk_B @ k1_xboole_0)))
% 0.39/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['54', '55'])).
% 0.39/0.59  thf('57', plain,
% 0.39/0.59      (![X36 : $i, X37 : $i]:
% 0.39/0.59         ((zip_tseitin_4 @ X36 @ X37) | ((X37) != (k1_xboole_0)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.59  thf('58', plain, (![X36 : $i]: (zip_tseitin_4 @ X36 @ k1_xboole_0)),
% 0.39/0.59      inference('simplify', [status(thm)], ['57'])).
% 0.39/0.59  thf('59', plain,
% 0.39/0.59      (((zip_tseitin_5 @ sk_D @ sk_B @ k1_xboole_0))
% 0.39/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('demod', [status(thm)], ['56', '58'])).
% 0.39/0.59  thf('60', plain,
% 0.39/0.59      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('demod', [status(thm)], ['53', '59'])).
% 0.39/0.59  thf(t64_relat_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( v1_relat_1 @ A ) =>
% 0.39/0.59       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.59           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.59         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.59  thf('61', plain,
% 0.39/0.59      (![X18 : $i]:
% 0.39/0.59         (((k1_relat_1 @ X18) != (k1_xboole_0))
% 0.39/0.59          | ((X18) = (k1_xboole_0))
% 0.39/0.59          | ~ (v1_relat_1 @ X18))),
% 0.39/0.59      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.39/0.59  thf('62', plain,
% 0.39/0.59      (((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.59         | ~ (v1_relat_1 @ sk_D)
% 0.39/0.59         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['60', '61'])).
% 0.39/0.59  thf('63', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.59      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.59  thf('64', plain,
% 0.39/0.59      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0))))
% 0.39/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('demod', [status(thm)], ['62', '63'])).
% 0.39/0.59  thf('65', plain,
% 0.39/0.59      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('simplify', [status(thm)], ['64'])).
% 0.39/0.59  thf('66', plain,
% 0.39/0.59      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.39/0.59         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('67', plain,
% 0.39/0.59      ((~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ sk_C_1))
% 0.39/0.59         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.39/0.59             (((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['65', '66'])).
% 0.39/0.59  thf('68', plain,
% 0.39/0.59      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('split', [status(esa)], ['36'])).
% 0.39/0.59  thf(t4_subset_1, axiom,
% 0.39/0.59    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.59  thf('69', plain,
% 0.39/0.59      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.39/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.59  thf('70', plain,
% 0.39/0.59      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.39/0.59         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 0.39/0.59          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.39/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.59  thf('71', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['69', '70'])).
% 0.39/0.59  thf(t60_relat_1, axiom,
% 0.39/0.59    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.39/0.59     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.39/0.59  thf('72', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.39/0.59  thf('73', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.59      inference('demod', [status(thm)], ['71', '72'])).
% 0.39/0.59  thf('74', plain,
% 0.39/0.59      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.39/0.59         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 0.39/0.59          | (v1_funct_2 @ X40 @ X38 @ X39)
% 0.39/0.59          | ~ (zip_tseitin_5 @ X40 @ X39 @ X38))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.59  thf('75', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (((X1) != (k1_xboole_0))
% 0.39/0.59          | ~ (zip_tseitin_5 @ k1_xboole_0 @ X0 @ X1)
% 0.39/0.59          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['73', '74'])).
% 0.39/0.59  thf('76', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.59          | ~ (zip_tseitin_5 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.59      inference('simplify', [status(thm)], ['75'])).
% 0.39/0.59  thf('77', plain, (![X36 : $i]: (zip_tseitin_4 @ X36 @ k1_xboole_0)),
% 0.39/0.59      inference('simplify', [status(thm)], ['57'])).
% 0.39/0.59  thf('78', plain,
% 0.39/0.59      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.39/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.59  thf('79', plain,
% 0.39/0.59      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.39/0.59         (~ (zip_tseitin_4 @ X41 @ X42)
% 0.39/0.59          | (zip_tseitin_5 @ X43 @ X41 @ X42)
% 0.39/0.59          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.59  thf('80', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((zip_tseitin_5 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_4 @ X0 @ X1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['78', '79'])).
% 0.39/0.59  thf('81', plain,
% 0.39/0.59      (![X0 : $i]: (zip_tseitin_5 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.39/0.59      inference('sup-', [status(thm)], ['77', '80'])).
% 0.39/0.59  thf('82', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.39/0.59      inference('demod', [status(thm)], ['76', '81'])).
% 0.39/0.59  thf('83', plain,
% 0.39/0.59      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['67', '68', '82'])).
% 0.39/0.59  thf('84', plain,
% 0.39/0.59      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.39/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.39/0.59  thf('85', plain,
% 0.39/0.59      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('split', [status(esa)], ['36'])).
% 0.39/0.59  thf('86', plain,
% 0.39/0.59      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((m1_subset_1 @ sk_D @ 
% 0.39/0.59               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('87', plain,
% 0.39/0.59      ((~ (m1_subset_1 @ sk_D @ 
% 0.39/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((m1_subset_1 @ sk_D @ 
% 0.39/0.59               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 0.39/0.59             (((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['85', '86'])).
% 0.39/0.59  thf('88', plain,
% 0.39/0.59      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.39/0.59         <= (~
% 0.39/0.59             ((m1_subset_1 @ sk_D @ 
% 0.39/0.59               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 0.39/0.59             (((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['84', '87'])).
% 0.39/0.59  thf('89', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.39/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('sup+', [status(thm)], ['44', '47'])).
% 0.39/0.59  thf('90', plain,
% 0.39/0.59      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.39/0.59       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.39/0.59      inference('demod', [status(thm)], ['88', '89'])).
% 0.39/0.59  thf('91', plain,
% 0.39/0.59      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 0.39/0.59       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ ((v1_funct_1 @ sk_D))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('92', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('split', [status(esa)], ['36'])).
% 0.39/0.59  thf('93', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)], ['4', '83', '90', '91', '92'])).
% 0.39/0.59  thf('94', plain, (((sk_B) != (k1_xboole_0))),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['37', '93'])).
% 0.39/0.59  thf('95', plain, ((zip_tseitin_5 @ sk_D @ sk_B @ sk_A)),
% 0.39/0.59      inference('simplify_reflect-', [status(thm)], ['35', '94'])).
% 0.39/0.59  thf('96', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.39/0.59      inference('demod', [status(thm)], ['30', '95'])).
% 0.39/0.59  thf('97', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.39/0.59      inference('demod', [status(thm)], ['21', '22', '23', '96'])).
% 0.39/0.59  thf('98', plain,
% 0.39/0.59      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((m1_subset_1 @ sk_D @ 
% 0.39/0.59               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('99', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['97', '98'])).
% 0.39/0.59  thf('100', plain,
% 0.39/0.59      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | 
% 0.39/0.59       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 0.39/0.59       ~ ((v1_funct_1 @ sk_D))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('101', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)], ['4', '99', '100'])).
% 0.39/0.59  thf('102', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['1', '101'])).
% 0.39/0.59  thf('103', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 0.39/0.59      inference('sup-', [status(thm)], ['5', '18'])).
% 0.39/0.59  thf('104', plain,
% 0.39/0.59      (![X44 : $i, X45 : $i]:
% 0.39/0.59         (~ (r1_tarski @ (k2_relat_1 @ X44) @ X45)
% 0.39/0.59          | (v1_funct_2 @ X44 @ (k1_relat_1 @ X44) @ X45)
% 0.39/0.59          | ~ (v1_funct_1 @ X44)
% 0.39/0.59          | ~ (v1_relat_1 @ X44))),
% 0.39/0.59      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.39/0.59  thf('105', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ sk_D)
% 0.39/0.59        | ~ (v1_funct_1 @ sk_D)
% 0.39/0.59        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C_1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['103', '104'])).
% 0.39/0.59  thf('106', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.59      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.59  thf('107', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('108', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.39/0.59      inference('demod', [status(thm)], ['30', '95'])).
% 0.39/0.59  thf('109', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.39/0.59      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 0.39/0.59  thf('110', plain, ($false), inference('demod', [status(thm)], ['102', '109'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
