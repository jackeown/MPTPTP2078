%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h0jttmqtk7

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:40 EST 2020

% Result     : Theorem 42.83s
% Output     : Refutation 42.83s
% Verified   : 
% Statistics : Number of formulae       :  236 (2033 expanded)
%              Number of leaves         :   47 ( 621 expanded)
%              Depth                    :   24
%              Number of atoms          : 1783 (27772 expanded)
%              Number of equality atoms :  125 (1687 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ) ),
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
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X46 @ X47 @ X45 @ X48 ) ) ) ),
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
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ) ),
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
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ( ( k2_partfun1 @ X50 @ X51 @ X49 @ X52 )
        = ( k7_relat_1 @ X49 @ X52 ) ) ) ),
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
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','11','12'])).

thf('14',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
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
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
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
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('32',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) @ sk_C_1 @ sk_B ) )
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
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('37',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
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
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
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
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
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
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('47',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('49',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('51',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ( ( k2_partfun1 @ X50 @ X51 @ X49 @ X52 )
        = ( k7_relat_1 @ X49 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('57',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('58',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('62',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('63',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['60','63'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('65',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ( ( k7_relat_1 @ X21 @ X22 )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['61','62'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','68'])).

thf('70',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','69'])).

thf('71',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('72',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('73',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('75',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('76',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('77',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','69'])).

thf('78',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('79',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('80',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('83',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('84',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X39
       != ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
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
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X38 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('90',plain,(
    ! [X37: $i] :
      ( zip_tseitin_0 @ X37 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('92',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
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
    inference(demod,[status(thm)],['32','42','47','70','71','72','73','74','75','76','77','78','95'])).

thf('97',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('98',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['96','97'])).

thf('99',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','98'])).

thf('100',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['27','99'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('101',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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

thf('104',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('105',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['14','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v5_relat_1 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('110',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['108','109'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('111',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v5_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('112',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['103','104'])).

thf('114',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['112','113'])).

thf(t99_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('115',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) ) @ ( k2_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t99_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('116',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['103','104'])).

thf('120',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('121',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('122',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['123'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('125',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X34 ) @ X35 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ X36 )
      | ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X46 @ X47 @ X45 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('134',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['127','136'])).

thf('138',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['107','137'])).

thf('139',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['13','138'])).

thf('140',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['107','137'])).

thf('141',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('142',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C_1 ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['14','106'])).

thf('144',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X39
       != ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('146',plain,
    ( ( sk_C_1 != sk_C_1 )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ sk_B @ sk_C_1 )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ sk_C_1 @ sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['107','137'])).

thf('149',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('150',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ sk_B @ sk_C_1 )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('152',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['112','113'])).

thf('154',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['123'])).

thf('155',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('156',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('162',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['160','163'])).

thf('165',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('166',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_D ) @ X0 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['153','166'])).

thf('168',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ( ( k7_relat_1 @ X21 @ X22 )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_D ) @ X0 ) )
      | ( ( k7_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_D ) @ X0 ) @ sk_B )
        = ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_D ) @ X0 ) @ sk_B )
      = ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('173',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('174',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_D ) @ X0 ) )
        = sk_B )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_D ) @ X0 ) )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup+',[status(thm)],['171','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_D ) @ X0 ) )
        = sk_B )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['152','179'])).

thf('181',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['82','83'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','98'])).

thf('184',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['182','183'])).

thf('185',plain,(
    zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['150','184'])).

thf('186',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['147','185'])).

thf('187',plain,(
    $false ),
    inference(demod,[status(thm)],['139','186'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h0jttmqtk7
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 42.83/43.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 42.83/43.10  % Solved by: fo/fo7.sh
% 42.83/43.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 42.83/43.10  % done 26510 iterations in 42.633s
% 42.83/43.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 42.83/43.10  % SZS output start Refutation
% 42.83/43.10  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 42.83/43.10  thf(sk_D_type, type, sk_D: $i).
% 42.83/43.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 42.83/43.10  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 42.83/43.10  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 42.83/43.10  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 42.83/43.10  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 42.83/43.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 42.83/43.10  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 42.83/43.10  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 42.83/43.10  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 42.83/43.10  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 42.83/43.10  thf(sk_B_type, type, sk_B: $i).
% 42.83/43.10  thf(sk_C_1_type, type, sk_C_1: $i).
% 42.83/43.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 42.83/43.10  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 42.83/43.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 42.83/43.10  thf(sk_A_type, type, sk_A: $i).
% 42.83/43.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 42.83/43.10  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 42.83/43.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 42.83/43.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 42.83/43.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 42.83/43.10  thf(t38_funct_2, conjecture,
% 42.83/43.10    (![A:$i,B:$i,C:$i,D:$i]:
% 42.83/43.10     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 42.83/43.10         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 42.83/43.10       ( ( r1_tarski @ C @ A ) =>
% 42.83/43.10         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 42.83/43.10           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 42.83/43.10             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 42.83/43.10             ( m1_subset_1 @
% 42.83/43.10               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 42.83/43.10               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 42.83/43.10  thf(zf_stmt_0, negated_conjecture,
% 42.83/43.10    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 42.83/43.10        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 42.83/43.10            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 42.83/43.10          ( ( r1_tarski @ C @ A ) =>
% 42.83/43.10            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 42.83/43.10              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 42.83/43.10                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 42.83/43.10                ( m1_subset_1 @
% 42.83/43.10                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 42.83/43.10                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 42.83/43.10    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 42.83/43.10  thf('0', plain,
% 42.83/43.10      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1))
% 42.83/43.10        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ 
% 42.83/43.10             sk_C_1 @ sk_B)
% 42.83/43.10        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ 
% 42.83/43.10             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B))))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.83/43.10  thf('1', plain,
% 42.83/43.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.83/43.10  thf(dt_k2_partfun1, axiom,
% 42.83/43.10    (![A:$i,B:$i,C:$i,D:$i]:
% 42.83/43.10     ( ( ( v1_funct_1 @ C ) & 
% 42.83/43.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 42.83/43.10       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 42.83/43.10         ( m1_subset_1 @
% 42.83/43.10           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 42.83/43.10           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 42.83/43.10  thf('2', plain,
% 42.83/43.10      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 42.83/43.10         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 42.83/43.10          | ~ (v1_funct_1 @ X45)
% 42.83/43.10          | (v1_funct_1 @ (k2_partfun1 @ X46 @ X47 @ X45 @ X48)))),
% 42.83/43.10      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 42.83/43.10  thf('3', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 42.83/43.10          | ~ (v1_funct_1 @ sk_D))),
% 42.83/43.10      inference('sup-', [status(thm)], ['1', '2'])).
% 42.83/43.10  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.83/43.10  thf('5', plain,
% 42.83/43.10      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 42.83/43.10      inference('demod', [status(thm)], ['3', '4'])).
% 42.83/43.10  thf('6', plain,
% 42.83/43.10      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ sk_C_1 @ 
% 42.83/43.10           sk_B)
% 42.83/43.10        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ 
% 42.83/43.10             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B))))),
% 42.83/43.10      inference('demod', [status(thm)], ['0', '5'])).
% 42.83/43.10  thf('7', plain,
% 42.83/43.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.83/43.10  thf(redefinition_k2_partfun1, axiom,
% 42.83/43.10    (![A:$i,B:$i,C:$i,D:$i]:
% 42.83/43.10     ( ( ( v1_funct_1 @ C ) & 
% 42.83/43.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 42.83/43.10       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 42.83/43.10  thf('8', plain,
% 42.83/43.10      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 42.83/43.10         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 42.83/43.10          | ~ (v1_funct_1 @ X49)
% 42.83/43.10          | ((k2_partfun1 @ X50 @ X51 @ X49 @ X52) = (k7_relat_1 @ X49 @ X52)))),
% 42.83/43.10      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 42.83/43.10  thf('9', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 42.83/43.10          | ~ (v1_funct_1 @ sk_D))),
% 42.83/43.10      inference('sup-', [status(thm)], ['7', '8'])).
% 42.83/43.10  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.83/43.10  thf('11', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 42.83/43.10      inference('demod', [status(thm)], ['9', '10'])).
% 42.83/43.10  thf('12', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 42.83/43.10      inference('demod', [status(thm)], ['9', '10'])).
% 42.83/43.10  thf('13', plain,
% 42.83/43.10      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C_1) @ sk_C_1 @ sk_B)
% 42.83/43.10        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C_1) @ 
% 42.83/43.10             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B))))),
% 42.83/43.10      inference('demod', [status(thm)], ['6', '11', '12'])).
% 42.83/43.10  thf('14', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.83/43.10  thf(d1_funct_2, axiom,
% 42.83/43.10    (![A:$i,B:$i,C:$i]:
% 42.83/43.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 42.83/43.10       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 42.83/43.10           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 42.83/43.10             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 42.83/43.10         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 42.83/43.10           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 42.83/43.10             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 42.83/43.10  thf(zf_stmt_1, axiom,
% 42.83/43.10    (![B:$i,A:$i]:
% 42.83/43.10     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 42.83/43.10       ( zip_tseitin_0 @ B @ A ) ))).
% 42.83/43.10  thf('15', plain,
% 42.83/43.10      (![X37 : $i, X38 : $i]:
% 42.83/43.10         ((zip_tseitin_0 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_1])).
% 42.83/43.10  thf('16', plain,
% 42.83/43.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.83/43.10  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 42.83/43.10  thf(zf_stmt_3, axiom,
% 42.83/43.10    (![C:$i,B:$i,A:$i]:
% 42.83/43.10     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 42.83/43.10       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 42.83/43.10  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 42.83/43.10  thf(zf_stmt_5, axiom,
% 42.83/43.10    (![A:$i,B:$i,C:$i]:
% 42.83/43.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 42.83/43.10       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 42.83/43.10         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 42.83/43.10           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 42.83/43.10             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 42.83/43.10  thf('17', plain,
% 42.83/43.10      (![X42 : $i, X43 : $i, X44 : $i]:
% 42.83/43.10         (~ (zip_tseitin_0 @ X42 @ X43)
% 42.83/43.10          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 42.83/43.10          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_5])).
% 42.83/43.10  thf('18', plain,
% 42.83/43.10      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 42.83/43.10      inference('sup-', [status(thm)], ['16', '17'])).
% 42.83/43.10  thf('19', plain,
% 42.83/43.10      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 42.83/43.10      inference('sup-', [status(thm)], ['15', '18'])).
% 42.83/43.10  thf('20', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.83/43.10  thf('21', plain,
% 42.83/43.10      (![X39 : $i, X40 : $i, X41 : $i]:
% 42.83/43.10         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 42.83/43.10          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 42.83/43.10          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_3])).
% 42.83/43.10  thf('22', plain,
% 42.83/43.10      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 42.83/43.10        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 42.83/43.10      inference('sup-', [status(thm)], ['20', '21'])).
% 42.83/43.10  thf('23', plain,
% 42.83/43.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.83/43.10  thf(redefinition_k1_relset_1, axiom,
% 42.83/43.10    (![A:$i,B:$i,C:$i]:
% 42.83/43.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 42.83/43.10       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 42.83/43.10  thf('24', plain,
% 42.83/43.10      (![X31 : $i, X32 : $i, X33 : $i]:
% 42.83/43.10         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 42.83/43.10          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 42.83/43.10      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 42.83/43.10  thf('25', plain,
% 42.83/43.10      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 42.83/43.10      inference('sup-', [status(thm)], ['23', '24'])).
% 42.83/43.10  thf('26', plain,
% 42.83/43.10      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 42.83/43.10      inference('demod', [status(thm)], ['22', '25'])).
% 42.83/43.10  thf('27', plain,
% 42.83/43.10      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 42.83/43.10      inference('sup-', [status(thm)], ['19', '26'])).
% 42.83/43.10  thf('28', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.83/43.10  thf('29', plain,
% 42.83/43.10      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 42.83/43.10      inference('split', [status(esa)], ['28'])).
% 42.83/43.10  thf('30', plain,
% 42.83/43.10      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('split', [status(esa)], ['28'])).
% 42.83/43.10  thf('31', plain,
% 42.83/43.10      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ sk_C_1 @ 
% 42.83/43.10           sk_B)
% 42.83/43.10        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ 
% 42.83/43.10             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B))))),
% 42.83/43.10      inference('demod', [status(thm)], ['0', '5'])).
% 42.83/43.10  thf('32', plain,
% 42.83/43.10      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C_1) @ 
% 42.83/43.10            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))
% 42.83/43.10         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ 
% 42.83/43.10              sk_C_1 @ sk_B)))
% 42.83/43.10         <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('sup-', [status(thm)], ['30', '31'])).
% 42.83/43.10  thf('33', plain,
% 42.83/43.10      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('split', [status(esa)], ['28'])).
% 42.83/43.10  thf('34', plain,
% 42.83/43.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.83/43.10  thf('35', plain,
% 42.83/43.10      (((m1_subset_1 @ sk_D @ 
% 42.83/43.10         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 42.83/43.10         <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('sup+', [status(thm)], ['33', '34'])).
% 42.83/43.10  thf(t113_zfmisc_1, axiom,
% 42.83/43.10    (![A:$i,B:$i]:
% 42.83/43.10     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 42.83/43.10       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 42.83/43.10  thf('36', plain,
% 42.83/43.10      (![X10 : $i, X11 : $i]:
% 42.83/43.10         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 42.83/43.10          | ((X10) != (k1_xboole_0)))),
% 42.83/43.10      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 42.83/43.10  thf('37', plain,
% 42.83/43.10      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 42.83/43.10      inference('simplify', [status(thm)], ['36'])).
% 42.83/43.10  thf('38', plain,
% 42.83/43.10      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 42.83/43.10         <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('demod', [status(thm)], ['35', '37'])).
% 42.83/43.10  thf(t3_subset, axiom,
% 42.83/43.10    (![A:$i,B:$i]:
% 42.83/43.10     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 42.83/43.10  thf('39', plain,
% 42.83/43.10      (![X12 : $i, X13 : $i]:
% 42.83/43.10         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 42.83/43.10      inference('cnf', [status(esa)], [t3_subset])).
% 42.83/43.10  thf('40', plain,
% 42.83/43.10      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('sup-', [status(thm)], ['38', '39'])).
% 42.83/43.10  thf(t3_xboole_1, axiom,
% 42.83/43.10    (![A:$i]:
% 42.83/43.10     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 42.83/43.10  thf('41', plain,
% 42.83/43.10      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 42.83/43.10      inference('cnf', [status(esa)], [t3_xboole_1])).
% 42.83/43.10  thf('42', plain,
% 42.83/43.10      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('sup-', [status(thm)], ['40', '41'])).
% 42.83/43.10  thf('43', plain,
% 42.83/43.10      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('split', [status(esa)], ['28'])).
% 42.83/43.10  thf('44', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.83/43.10  thf('45', plain,
% 42.83/43.10      (((r1_tarski @ sk_C_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('sup+', [status(thm)], ['43', '44'])).
% 42.83/43.10  thf('46', plain,
% 42.83/43.10      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 42.83/43.10      inference('cnf', [status(esa)], [t3_xboole_1])).
% 42.83/43.10  thf('47', plain,
% 42.83/43.10      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('sup-', [status(thm)], ['45', '46'])).
% 42.83/43.10  thf('48', plain,
% 42.83/43.10      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('sup-', [status(thm)], ['40', '41'])).
% 42.83/43.10  thf('49', plain, ((v1_funct_1 @ sk_D)),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.83/43.10  thf('50', plain,
% 42.83/43.10      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('sup+', [status(thm)], ['48', '49'])).
% 42.83/43.10  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 42.83/43.10  thf('51', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 42.83/43.10      inference('cnf', [status(esa)], [t2_xboole_1])).
% 42.83/43.10  thf('52', plain,
% 42.83/43.10      (![X12 : $i, X14 : $i]:
% 42.83/43.10         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 42.83/43.10      inference('cnf', [status(esa)], [t3_subset])).
% 42.83/43.10  thf('53', plain,
% 42.83/43.10      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['51', '52'])).
% 42.83/43.10  thf('54', plain,
% 42.83/43.10      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 42.83/43.10         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 42.83/43.10          | ~ (v1_funct_1 @ X49)
% 42.83/43.10          | ((k2_partfun1 @ X50 @ X51 @ X49 @ X52) = (k7_relat_1 @ X49 @ X52)))),
% 42.83/43.10      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 42.83/43.10  thf('55', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.83/43.10         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 42.83/43.10            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 42.83/43.10          | ~ (v1_funct_1 @ k1_xboole_0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['53', '54'])).
% 42.83/43.10  thf('56', plain,
% 42.83/43.10      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['51', '52'])).
% 42.83/43.10  thf(cc2_relset_1, axiom,
% 42.83/43.10    (![A:$i,B:$i,C:$i]:
% 42.83/43.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 42.83/43.10       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 42.83/43.10  thf('57', plain,
% 42.83/43.10      (![X28 : $i, X29 : $i, X30 : $i]:
% 42.83/43.10         ((v4_relat_1 @ X28 @ X29)
% 42.83/43.10          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 42.83/43.10      inference('cnf', [status(esa)], [cc2_relset_1])).
% 42.83/43.10  thf('58', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 42.83/43.10      inference('sup-', [status(thm)], ['56', '57'])).
% 42.83/43.10  thf(d18_relat_1, axiom,
% 42.83/43.10    (![A:$i,B:$i]:
% 42.83/43.10     ( ( v1_relat_1 @ B ) =>
% 42.83/43.10       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 42.83/43.10  thf('59', plain,
% 42.83/43.10      (![X15 : $i, X16 : $i]:
% 42.83/43.10         (~ (v4_relat_1 @ X15 @ X16)
% 42.83/43.10          | (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 42.83/43.10          | ~ (v1_relat_1 @ X15))),
% 42.83/43.10      inference('cnf', [status(esa)], [d18_relat_1])).
% 42.83/43.10  thf('60', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         (~ (v1_relat_1 @ k1_xboole_0)
% 42.83/43.10          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['58', '59'])).
% 42.83/43.10  thf('61', plain,
% 42.83/43.10      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['51', '52'])).
% 42.83/43.10  thf(cc1_relset_1, axiom,
% 42.83/43.10    (![A:$i,B:$i,C:$i]:
% 42.83/43.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 42.83/43.10       ( v1_relat_1 @ C ) ))).
% 42.83/43.10  thf('62', plain,
% 42.83/43.10      (![X25 : $i, X26 : $i, X27 : $i]:
% 42.83/43.10         ((v1_relat_1 @ X25)
% 42.83/43.10          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 42.83/43.10      inference('cnf', [status(esa)], [cc1_relset_1])).
% 42.83/43.10  thf('63', plain, ((v1_relat_1 @ k1_xboole_0)),
% 42.83/43.10      inference('sup-', [status(thm)], ['61', '62'])).
% 42.83/43.10  thf('64', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 42.83/43.10      inference('demod', [status(thm)], ['60', '63'])).
% 42.83/43.10  thf(t97_relat_1, axiom,
% 42.83/43.10    (![A:$i,B:$i]:
% 42.83/43.10     ( ( v1_relat_1 @ B ) =>
% 42.83/43.10       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 42.83/43.10         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 42.83/43.10  thf('65', plain,
% 42.83/43.10      (![X21 : $i, X22 : $i]:
% 42.83/43.10         (~ (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 42.83/43.10          | ((k7_relat_1 @ X21 @ X22) = (X21))
% 42.83/43.10          | ~ (v1_relat_1 @ X21))),
% 42.83/43.10      inference('cnf', [status(esa)], [t97_relat_1])).
% 42.83/43.10  thf('66', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         (~ (v1_relat_1 @ k1_xboole_0)
% 42.83/43.10          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 42.83/43.10      inference('sup-', [status(thm)], ['64', '65'])).
% 42.83/43.10  thf('67', plain, ((v1_relat_1 @ k1_xboole_0)),
% 42.83/43.10      inference('sup-', [status(thm)], ['61', '62'])).
% 42.83/43.10  thf('68', plain,
% 42.83/43.10      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 42.83/43.10      inference('demod', [status(thm)], ['66', '67'])).
% 42.83/43.10  thf('69', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.83/43.10         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 42.83/43.10          | ~ (v1_funct_1 @ k1_xboole_0))),
% 42.83/43.10      inference('demod', [status(thm)], ['55', '68'])).
% 42.83/43.10  thf('70', plain,
% 42.83/43.10      ((![X0 : $i, X1 : $i, X2 : $i]:
% 42.83/43.10          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 42.83/43.10         <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('sup-', [status(thm)], ['50', '69'])).
% 42.83/43.10  thf('71', plain,
% 42.83/43.10      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('sup-', [status(thm)], ['45', '46'])).
% 42.83/43.10  thf('72', plain,
% 42.83/43.10      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 42.83/43.10      inference('simplify', [status(thm)], ['36'])).
% 42.83/43.10  thf('73', plain,
% 42.83/43.10      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['51', '52'])).
% 42.83/43.10  thf('74', plain,
% 42.83/43.10      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('split', [status(esa)], ['28'])).
% 42.83/43.10  thf('75', plain,
% 42.83/43.10      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('sup-', [status(thm)], ['40', '41'])).
% 42.83/43.10  thf('76', plain,
% 42.83/43.10      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('sup-', [status(thm)], ['45', '46'])).
% 42.83/43.10  thf('77', plain,
% 42.83/43.10      ((![X0 : $i, X1 : $i, X2 : $i]:
% 42.83/43.10          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 42.83/43.10         <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('sup-', [status(thm)], ['50', '69'])).
% 42.83/43.10  thf('78', plain,
% 42.83/43.10      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 42.83/43.10      inference('sup-', [status(thm)], ['45', '46'])).
% 42.83/43.10  thf('79', plain,
% 42.83/43.10      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['51', '52'])).
% 42.83/43.10  thf('80', plain,
% 42.83/43.10      (![X31 : $i, X32 : $i, X33 : $i]:
% 42.83/43.10         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 42.83/43.10          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 42.83/43.10      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 42.83/43.10  thf('81', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i]:
% 42.83/43.10         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['79', '80'])).
% 42.83/43.10  thf('82', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 42.83/43.10      inference('demod', [status(thm)], ['60', '63'])).
% 42.83/43.10  thf('83', plain,
% 42.83/43.10      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 42.83/43.10      inference('cnf', [status(esa)], [t3_xboole_1])).
% 42.83/43.10  thf('84', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['82', '83'])).
% 42.83/43.10  thf('85', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i]:
% 42.83/43.10         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 42.83/43.10      inference('demod', [status(thm)], ['81', '84'])).
% 42.83/43.10  thf('86', plain,
% 42.83/43.10      (![X39 : $i, X40 : $i, X41 : $i]:
% 42.83/43.10         (((X39) != (k1_relset_1 @ X39 @ X40 @ X41))
% 42.83/43.10          | (v1_funct_2 @ X41 @ X39 @ X40)
% 42.83/43.10          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_3])).
% 42.83/43.10  thf('87', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i]:
% 42.83/43.10         (((X1) != (k1_xboole_0))
% 42.83/43.10          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 42.83/43.10          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['85', '86'])).
% 42.83/43.10  thf('88', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 42.83/43.10          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 42.83/43.10      inference('simplify', [status(thm)], ['87'])).
% 42.83/43.10  thf('89', plain,
% 42.83/43.10      (![X37 : $i, X38 : $i]:
% 42.83/43.10         ((zip_tseitin_0 @ X37 @ X38) | ((X38) != (k1_xboole_0)))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_1])).
% 42.83/43.10  thf('90', plain, (![X37 : $i]: (zip_tseitin_0 @ X37 @ k1_xboole_0)),
% 42.83/43.10      inference('simplify', [status(thm)], ['89'])).
% 42.83/43.10  thf('91', plain,
% 42.83/43.10      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['51', '52'])).
% 42.83/43.10  thf('92', plain,
% 42.83/43.10      (![X42 : $i, X43 : $i, X44 : $i]:
% 42.83/43.10         (~ (zip_tseitin_0 @ X42 @ X43)
% 42.83/43.10          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 42.83/43.10          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_5])).
% 42.83/43.10  thf('93', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i]:
% 42.83/43.10         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 42.83/43.10      inference('sup-', [status(thm)], ['91', '92'])).
% 42.83/43.10  thf('94', plain,
% 42.83/43.10      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 42.83/43.10      inference('sup-', [status(thm)], ['90', '93'])).
% 42.83/43.10  thf('95', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 42.83/43.10      inference('demod', [status(thm)], ['88', '94'])).
% 42.83/43.10  thf('96', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 42.83/43.10      inference('demod', [status(thm)],
% 42.83/43.10                ['32', '42', '47', '70', '71', '72', '73', '74', '75', '76', 
% 42.83/43.10                 '77', '78', '95'])).
% 42.83/43.10  thf('97', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 42.83/43.10      inference('split', [status(esa)], ['28'])).
% 42.83/43.10  thf('98', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 42.83/43.10      inference('sat_resolution*', [status(thm)], ['96', '97'])).
% 42.83/43.10  thf('99', plain, (((sk_B) != (k1_xboole_0))),
% 42.83/43.10      inference('simpl_trail', [status(thm)], ['29', '98'])).
% 42.83/43.10  thf('100', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 42.83/43.10      inference('simplify_reflect-', [status(thm)], ['27', '99'])).
% 42.83/43.10  thf(t91_relat_1, axiom,
% 42.83/43.10    (![A:$i,B:$i]:
% 42.83/43.10     ( ( v1_relat_1 @ B ) =>
% 42.83/43.10       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 42.83/43.10         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 42.83/43.10  thf('101', plain,
% 42.83/43.10      (![X19 : $i, X20 : $i]:
% 42.83/43.10         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 42.83/43.10          | ((k1_relat_1 @ (k7_relat_1 @ X20 @ X19)) = (X19))
% 42.83/43.10          | ~ (v1_relat_1 @ X20))),
% 42.83/43.10      inference('cnf', [status(esa)], [t91_relat_1])).
% 42.83/43.10  thf('102', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         (~ (r1_tarski @ X0 @ sk_A)
% 42.83/43.10          | ~ (v1_relat_1 @ sk_D)
% 42.83/43.10          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 42.83/43.10      inference('sup-', [status(thm)], ['100', '101'])).
% 42.83/43.10  thf('103', plain,
% 42.83/43.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.83/43.10  thf('104', plain,
% 42.83/43.10      (![X25 : $i, X26 : $i, X27 : $i]:
% 42.83/43.10         ((v1_relat_1 @ X25)
% 42.83/43.10          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 42.83/43.10      inference('cnf', [status(esa)], [cc1_relset_1])).
% 42.83/43.10  thf('105', plain, ((v1_relat_1 @ sk_D)),
% 42.83/43.10      inference('sup-', [status(thm)], ['103', '104'])).
% 42.83/43.10  thf('106', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         (~ (r1_tarski @ X0 @ sk_A)
% 42.83/43.10          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 42.83/43.10      inference('demod', [status(thm)], ['102', '105'])).
% 42.83/43.10  thf('107', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C_1)) = (sk_C_1))),
% 42.83/43.10      inference('sup-', [status(thm)], ['14', '106'])).
% 42.83/43.10  thf('108', plain,
% 42.83/43.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.83/43.10  thf('109', plain,
% 42.83/43.10      (![X28 : $i, X29 : $i, X30 : $i]:
% 42.83/43.10         ((v5_relat_1 @ X28 @ X30)
% 42.83/43.10          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 42.83/43.10      inference('cnf', [status(esa)], [cc2_relset_1])).
% 42.83/43.10  thf('110', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 42.83/43.10      inference('sup-', [status(thm)], ['108', '109'])).
% 42.83/43.10  thf(d19_relat_1, axiom,
% 42.83/43.10    (![A:$i,B:$i]:
% 42.83/43.10     ( ( v1_relat_1 @ B ) =>
% 42.83/43.10       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 42.83/43.10  thf('111', plain,
% 42.83/43.10      (![X17 : $i, X18 : $i]:
% 42.83/43.10         (~ (v5_relat_1 @ X17 @ X18)
% 42.83/43.10          | (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 42.83/43.10          | ~ (v1_relat_1 @ X17))),
% 42.83/43.10      inference('cnf', [status(esa)], [d19_relat_1])).
% 42.83/43.10  thf('112', plain,
% 42.83/43.10      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 42.83/43.10      inference('sup-', [status(thm)], ['110', '111'])).
% 42.83/43.10  thf('113', plain, ((v1_relat_1 @ sk_D)),
% 42.83/43.10      inference('sup-', [status(thm)], ['103', '104'])).
% 42.83/43.10  thf('114', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 42.83/43.10      inference('demod', [status(thm)], ['112', '113'])).
% 42.83/43.10  thf(t99_relat_1, axiom,
% 42.83/43.10    (![A:$i,B:$i]:
% 42.83/43.10     ( ( v1_relat_1 @ B ) =>
% 42.83/43.10       ( r1_tarski @
% 42.83/43.10         ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ))).
% 42.83/43.10  thf('115', plain,
% 42.83/43.10      (![X23 : $i, X24 : $i]:
% 42.83/43.10         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X23 @ X24)) @ 
% 42.83/43.10           (k2_relat_1 @ X23))
% 42.83/43.10          | ~ (v1_relat_1 @ X23))),
% 42.83/43.10      inference('cnf', [status(esa)], [t99_relat_1])).
% 42.83/43.10  thf(t1_xboole_1, axiom,
% 42.83/43.10    (![A:$i,B:$i,C:$i]:
% 42.83/43.10     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 42.83/43.10       ( r1_tarski @ A @ C ) ))).
% 42.83/43.10  thf('116', plain,
% 42.83/43.10      (![X4 : $i, X5 : $i, X6 : $i]:
% 42.83/43.10         (~ (r1_tarski @ X4 @ X5)
% 42.83/43.10          | ~ (r1_tarski @ X5 @ X6)
% 42.83/43.10          | (r1_tarski @ X4 @ X6))),
% 42.83/43.10      inference('cnf', [status(esa)], [t1_xboole_1])).
% 42.83/43.10  thf('117', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.83/43.10         (~ (v1_relat_1 @ X0)
% 42.83/43.10          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 42.83/43.10          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X2))),
% 42.83/43.10      inference('sup-', [status(thm)], ['115', '116'])).
% 42.83/43.10  thf('118', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)
% 42.83/43.10          | ~ (v1_relat_1 @ sk_D))),
% 42.83/43.10      inference('sup-', [status(thm)], ['114', '117'])).
% 42.83/43.10  thf('119', plain, ((v1_relat_1 @ sk_D)),
% 42.83/43.10      inference('sup-', [status(thm)], ['103', '104'])).
% 42.83/43.10  thf('120', plain,
% 42.83/43.10      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 42.83/43.10      inference('demod', [status(thm)], ['118', '119'])).
% 42.83/43.10  thf(d3_tarski, axiom,
% 42.83/43.10    (![A:$i,B:$i]:
% 42.83/43.10     ( ( r1_tarski @ A @ B ) <=>
% 42.83/43.10       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 42.83/43.10  thf('121', plain,
% 42.83/43.10      (![X1 : $i, X3 : $i]:
% 42.83/43.10         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 42.83/43.10      inference('cnf', [status(esa)], [d3_tarski])).
% 42.83/43.10  thf('122', plain,
% 42.83/43.10      (![X1 : $i, X3 : $i]:
% 42.83/43.10         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 42.83/43.10      inference('cnf', [status(esa)], [d3_tarski])).
% 42.83/43.10  thf('123', plain,
% 42.83/43.10      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['121', '122'])).
% 42.83/43.10  thf('124', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 42.83/43.10      inference('simplify', [status(thm)], ['123'])).
% 42.83/43.10  thf(t11_relset_1, axiom,
% 42.83/43.10    (![A:$i,B:$i,C:$i]:
% 42.83/43.10     ( ( v1_relat_1 @ C ) =>
% 42.83/43.10       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 42.83/43.10           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 42.83/43.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 42.83/43.10  thf('125', plain,
% 42.83/43.10      (![X34 : $i, X35 : $i, X36 : $i]:
% 42.83/43.10         (~ (r1_tarski @ (k1_relat_1 @ X34) @ X35)
% 42.83/43.10          | ~ (r1_tarski @ (k2_relat_1 @ X34) @ X36)
% 42.83/43.10          | (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 42.83/43.10          | ~ (v1_relat_1 @ X34))),
% 42.83/43.10      inference('cnf', [status(esa)], [t11_relset_1])).
% 42.83/43.10  thf('126', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i]:
% 42.83/43.10         (~ (v1_relat_1 @ X0)
% 42.83/43.10          | (m1_subset_1 @ X0 @ 
% 42.83/43.10             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 42.83/43.10          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 42.83/43.10      inference('sup-', [status(thm)], ['124', '125'])).
% 42.83/43.10  thf('127', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 42.83/43.10           (k1_zfmisc_1 @ 
% 42.83/43.10            (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))
% 42.83/43.10          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 42.83/43.10      inference('sup-', [status(thm)], ['120', '126'])).
% 42.83/43.10  thf('128', plain,
% 42.83/43.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.83/43.10  thf('129', plain,
% 42.83/43.10      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 42.83/43.10         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 42.83/43.10          | ~ (v1_funct_1 @ X45)
% 42.83/43.10          | (m1_subset_1 @ (k2_partfun1 @ X46 @ X47 @ X45 @ X48) @ 
% 42.83/43.10             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 42.83/43.10      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 42.83/43.10  thf('130', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 42.83/43.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 42.83/43.10          | ~ (v1_funct_1 @ sk_D))),
% 42.83/43.10      inference('sup-', [status(thm)], ['128', '129'])).
% 42.83/43.10  thf('131', plain, ((v1_funct_1 @ sk_D)),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.83/43.10  thf('132', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 42.83/43.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 42.83/43.10      inference('demod', [status(thm)], ['130', '131'])).
% 42.83/43.10  thf('133', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 42.83/43.10      inference('demod', [status(thm)], ['9', '10'])).
% 42.83/43.10  thf('134', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 42.83/43.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 42.83/43.10      inference('demod', [status(thm)], ['132', '133'])).
% 42.83/43.10  thf('135', plain,
% 42.83/43.10      (![X25 : $i, X26 : $i, X27 : $i]:
% 42.83/43.10         ((v1_relat_1 @ X25)
% 42.83/43.10          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 42.83/43.10      inference('cnf', [status(esa)], [cc1_relset_1])).
% 42.83/43.10  thf('136', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['134', '135'])).
% 42.83/43.10  thf('137', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 42.83/43.10          (k1_zfmisc_1 @ 
% 42.83/43.10           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 42.83/43.10      inference('demod', [status(thm)], ['127', '136'])).
% 42.83/43.10  thf('138', plain,
% 42.83/43.10      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C_1) @ 
% 42.83/43.10        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 42.83/43.10      inference('sup+', [status(thm)], ['107', '137'])).
% 42.83/43.10  thf('139', plain,
% 42.83/43.10      (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C_1) @ sk_C_1 @ sk_B)),
% 42.83/43.10      inference('demod', [status(thm)], ['13', '138'])).
% 42.83/43.10  thf('140', plain,
% 42.83/43.10      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C_1) @ 
% 42.83/43.10        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 42.83/43.10      inference('sup+', [status(thm)], ['107', '137'])).
% 42.83/43.10  thf('141', plain,
% 42.83/43.10      (![X31 : $i, X32 : $i, X33 : $i]:
% 42.83/43.10         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 42.83/43.10          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 42.83/43.10      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 42.83/43.10  thf('142', plain,
% 42.83/43.10      (((k1_relset_1 @ sk_C_1 @ sk_B @ (k7_relat_1 @ sk_D @ sk_C_1))
% 42.83/43.10         = (k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C_1)))),
% 42.83/43.10      inference('sup-', [status(thm)], ['140', '141'])).
% 42.83/43.10  thf('143', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C_1)) = (sk_C_1))),
% 42.83/43.10      inference('sup-', [status(thm)], ['14', '106'])).
% 42.83/43.10  thf('144', plain,
% 42.83/43.10      (((k1_relset_1 @ sk_C_1 @ sk_B @ (k7_relat_1 @ sk_D @ sk_C_1)) = (sk_C_1))),
% 42.83/43.10      inference('demod', [status(thm)], ['142', '143'])).
% 42.83/43.10  thf('145', plain,
% 42.83/43.10      (![X39 : $i, X40 : $i, X41 : $i]:
% 42.83/43.10         (((X39) != (k1_relset_1 @ X39 @ X40 @ X41))
% 42.83/43.10          | (v1_funct_2 @ X41 @ X39 @ X40)
% 42.83/43.10          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_3])).
% 42.83/43.10  thf('146', plain,
% 42.83/43.10      ((((sk_C_1) != (sk_C_1))
% 42.83/43.10        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C_1) @ sk_B @ sk_C_1)
% 42.83/43.10        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C_1) @ sk_C_1 @ sk_B))),
% 42.83/43.10      inference('sup-', [status(thm)], ['144', '145'])).
% 42.83/43.10  thf('147', plain,
% 42.83/43.10      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C_1) @ sk_C_1 @ sk_B)
% 42.83/43.10        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C_1) @ sk_B @ sk_C_1))),
% 42.83/43.10      inference('simplify', [status(thm)], ['146'])).
% 42.83/43.10  thf('148', plain,
% 42.83/43.10      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C_1) @ 
% 42.83/43.10        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 42.83/43.10      inference('sup+', [status(thm)], ['107', '137'])).
% 42.83/43.10  thf('149', plain,
% 42.83/43.10      (![X42 : $i, X43 : $i, X44 : $i]:
% 42.83/43.10         (~ (zip_tseitin_0 @ X42 @ X43)
% 42.83/43.10          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 42.83/43.10          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_5])).
% 42.83/43.10  thf('150', plain,
% 42.83/43.10      (((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C_1) @ sk_B @ sk_C_1)
% 42.83/43.10        | ~ (zip_tseitin_0 @ sk_B @ sk_C_1))),
% 42.83/43.10      inference('sup-', [status(thm)], ['148', '149'])).
% 42.83/43.10  thf('151', plain,
% 42.83/43.10      (![X10 : $i, X11 : $i]:
% 42.83/43.10         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 42.83/43.10          | ((X11) != (k1_xboole_0)))),
% 42.83/43.10      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 42.83/43.10  thf('152', plain,
% 42.83/43.10      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 42.83/43.10      inference('simplify', [status(thm)], ['151'])).
% 42.83/43.10  thf('153', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 42.83/43.10      inference('demod', [status(thm)], ['112', '113'])).
% 42.83/43.10  thf('154', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 42.83/43.10      inference('simplify', [status(thm)], ['123'])).
% 42.83/43.10  thf('155', plain,
% 42.83/43.10      (![X12 : $i, X14 : $i]:
% 42.83/43.10         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 42.83/43.10      inference('cnf', [status(esa)], [t3_subset])).
% 42.83/43.10  thf('156', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['154', '155'])).
% 42.83/43.10  thf('157', plain,
% 42.83/43.10      (![X28 : $i, X29 : $i, X30 : $i]:
% 42.83/43.10         ((v4_relat_1 @ X28 @ X29)
% 42.83/43.10          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 42.83/43.10      inference('cnf', [status(esa)], [cc2_relset_1])).
% 42.83/43.10  thf('158', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 42.83/43.10      inference('sup-', [status(thm)], ['156', '157'])).
% 42.83/43.10  thf('159', plain,
% 42.83/43.10      (![X15 : $i, X16 : $i]:
% 42.83/43.10         (~ (v4_relat_1 @ X15 @ X16)
% 42.83/43.10          | (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 42.83/43.10          | ~ (v1_relat_1 @ X15))),
% 42.83/43.10      inference('cnf', [status(esa)], [d18_relat_1])).
% 42.83/43.10  thf('160', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i]:
% 42.83/43.10         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 42.83/43.10          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['158', '159'])).
% 42.83/43.10  thf('161', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['154', '155'])).
% 42.83/43.10  thf('162', plain,
% 42.83/43.10      (![X25 : $i, X26 : $i, X27 : $i]:
% 42.83/43.10         ((v1_relat_1 @ X25)
% 42.83/43.10          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 42.83/43.10      inference('cnf', [status(esa)], [cc1_relset_1])).
% 42.83/43.10  thf('163', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['161', '162'])).
% 42.83/43.10  thf('164', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i]:
% 42.83/43.10         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 42.83/43.10      inference('demod', [status(thm)], ['160', '163'])).
% 42.83/43.10  thf('165', plain,
% 42.83/43.10      (![X4 : $i, X5 : $i, X6 : $i]:
% 42.83/43.10         (~ (r1_tarski @ X4 @ X5)
% 42.83/43.10          | ~ (r1_tarski @ X5 @ X6)
% 42.83/43.10          | (r1_tarski @ X4 @ X6))),
% 42.83/43.10      inference('cnf', [status(esa)], [t1_xboole_1])).
% 42.83/43.10  thf('166', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.83/43.10         ((r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X2)
% 42.83/43.10          | ~ (r1_tarski @ X0 @ X2))),
% 42.83/43.10      inference('sup-', [status(thm)], ['164', '165'])).
% 42.83/43.10  thf('167', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         (r1_tarski @ 
% 42.83/43.10          (k1_relat_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_D) @ X0)) @ sk_B)),
% 42.83/43.10      inference('sup-', [status(thm)], ['153', '166'])).
% 42.83/43.10  thf('168', plain,
% 42.83/43.10      (![X21 : $i, X22 : $i]:
% 42.83/43.10         (~ (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 42.83/43.10          | ((k7_relat_1 @ X21 @ X22) = (X21))
% 42.83/43.10          | ~ (v1_relat_1 @ X21))),
% 42.83/43.10      inference('cnf', [status(esa)], [t97_relat_1])).
% 42.83/43.10  thf('169', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         (~ (v1_relat_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_D) @ X0))
% 42.83/43.10          | ((k7_relat_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_D) @ X0) @ sk_B)
% 42.83/43.10              = (k2_zfmisc_1 @ (k2_relat_1 @ sk_D) @ X0)))),
% 42.83/43.10      inference('sup-', [status(thm)], ['167', '168'])).
% 42.83/43.10  thf('170', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['161', '162'])).
% 42.83/43.10  thf('171', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         ((k7_relat_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_D) @ X0) @ sk_B)
% 42.83/43.10           = (k2_zfmisc_1 @ (k2_relat_1 @ sk_D) @ X0))),
% 42.83/43.10      inference('demod', [status(thm)], ['169', '170'])).
% 42.83/43.10  thf('172', plain,
% 42.83/43.10      (![X37 : $i, X38 : $i]:
% 42.83/43.10         ((zip_tseitin_0 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 42.83/43.10      inference('cnf', [status(esa)], [zf_stmt_1])).
% 42.83/43.10  thf('173', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 42.83/43.10      inference('cnf', [status(esa)], [t2_xboole_1])).
% 42.83/43.10  thf('174', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.83/43.10         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 42.83/43.10      inference('sup+', [status(thm)], ['172', '173'])).
% 42.83/43.10  thf('175', plain,
% 42.83/43.10      (![X19 : $i, X20 : $i]:
% 42.83/43.10         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 42.83/43.10          | ((k1_relat_1 @ (k7_relat_1 @ X20 @ X19)) = (X19))
% 42.83/43.10          | ~ (v1_relat_1 @ X20))),
% 42.83/43.10      inference('cnf', [status(esa)], [t91_relat_1])).
% 42.83/43.10  thf('176', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.83/43.10         ((zip_tseitin_0 @ X1 @ X2)
% 42.83/43.10          | ~ (v1_relat_1 @ X0)
% 42.83/43.10          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) = (X1)))),
% 42.83/43.10      inference('sup-', [status(thm)], ['174', '175'])).
% 42.83/43.10  thf('177', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i]:
% 42.83/43.10         (((k1_relat_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_D) @ X0)) = (sk_B))
% 42.83/43.10          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_D) @ X0))
% 42.83/43.10          | (zip_tseitin_0 @ sk_B @ X1))),
% 42.83/43.10      inference('sup+', [status(thm)], ['171', '176'])).
% 42.83/43.10  thf('178', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['161', '162'])).
% 42.83/43.10  thf('179', plain,
% 42.83/43.10      (![X0 : $i, X1 : $i]:
% 42.83/43.10         (((k1_relat_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_D) @ X0)) = (sk_B))
% 42.83/43.10          | (zip_tseitin_0 @ sk_B @ X1))),
% 42.83/43.10      inference('demod', [status(thm)], ['177', '178'])).
% 42.83/43.10  thf('180', plain,
% 42.83/43.10      (![X0 : $i]:
% 42.83/43.10         (((k1_relat_1 @ k1_xboole_0) = (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 42.83/43.10      inference('sup+', [status(thm)], ['152', '179'])).
% 42.83/43.10  thf('181', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 42.83/43.10      inference('sup-', [status(thm)], ['82', '83'])).
% 42.83/43.10  thf('182', plain,
% 42.83/43.10      (![X0 : $i]: (((k1_xboole_0) = (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 42.83/43.10      inference('demod', [status(thm)], ['180', '181'])).
% 42.83/43.10  thf('183', plain, (((sk_B) != (k1_xboole_0))),
% 42.83/43.10      inference('simpl_trail', [status(thm)], ['29', '98'])).
% 42.83/43.10  thf('184', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 42.83/43.10      inference('simplify_reflect-', [status(thm)], ['182', '183'])).
% 42.83/43.10  thf('185', plain,
% 42.83/43.10      ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C_1) @ sk_B @ sk_C_1)),
% 42.83/43.10      inference('demod', [status(thm)], ['150', '184'])).
% 42.83/43.10  thf('186', plain,
% 42.83/43.10      ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C_1) @ sk_C_1 @ sk_B)),
% 42.83/43.10      inference('demod', [status(thm)], ['147', '185'])).
% 42.83/43.10  thf('187', plain, ($false), inference('demod', [status(thm)], ['139', '186'])).
% 42.83/43.10  
% 42.83/43.10  % SZS output end Refutation
% 42.83/43.10  
% 42.83/43.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
