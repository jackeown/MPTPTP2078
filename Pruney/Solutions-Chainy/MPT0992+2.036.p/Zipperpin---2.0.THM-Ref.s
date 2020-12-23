%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oB1zQDCvi6

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:39 EST 2020

% Result     : Theorem 17.31s
% Output     : Refutation 17.31s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 869 expanded)
%              Number of leaves         :   43 ( 270 expanded)
%              Depth                    :   20
%              Number of atoms          : 1407 (12908 expanded)
%              Number of equality atoms :  108 ( 810 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('37',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
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
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
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
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
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
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('47',plain,
    ( ( sk_C = k1_xboole_0 )
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
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k2_partfun1 @ X44 @ X45 @ X43 @ X46 )
        = ( k7_relat_1 @ X43 @ X46 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X18 @ X19 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('57',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('60',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
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
    inference('sup-',[status(thm)],['50','63'])).

thf('65',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('66',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('67',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('68',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('69',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('70',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('71',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','63'])).

thf('72',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('73',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('74',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
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
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('78',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('81',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','60'])).

thf('82',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','82'])).

thf('84',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('88',plain,(
    ! [X31: $i] :
      ( zip_tseitin_0 @ X31 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('90',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['86','92'])).

thf('94',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['32','42','47','64','65','66','67','68','69','70','71','72','93'])).

thf('95',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('96',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['94','95'])).

thf('97',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','96'])).

thf('98',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['27','97'])).

thf('99',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('102',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('103',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X18 @ X19 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('110',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['101','102'])).

thf('114',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('116',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('117',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('119',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('122',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['120','123'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('125',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X47 ) @ X48 )
      | ( v1_funct_2 @ X47 @ ( k1_relat_1 @ X47 ) @ X48 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('128',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('130',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['126','127','130'])).

thf('132',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['105','131'])).

thf('133',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','132'])).

thf('134',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','104'])).

thf('135',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['120','123'])).

thf('136',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X47 ) @ X48 )
      | ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X47 ) @ X48 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('139',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('140',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['134','140'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['133','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oB1zQDCvi6
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 17.31/17.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.31/17.49  % Solved by: fo/fo7.sh
% 17.31/17.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.31/17.49  % done 13550 iterations in 17.029s
% 17.31/17.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.31/17.49  % SZS output start Refutation
% 17.31/17.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 17.31/17.49  thf(sk_C_type, type, sk_C: $i).
% 17.31/17.49  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 17.31/17.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 17.31/17.49  thf(sk_A_type, type, sk_A: $i).
% 17.31/17.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 17.31/17.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 17.31/17.49  thf(sk_B_type, type, sk_B: $i).
% 17.31/17.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 17.31/17.49  thf(sk_D_type, type, sk_D: $i).
% 17.31/17.49  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 17.31/17.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 17.31/17.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 17.31/17.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 17.31/17.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 17.31/17.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.31/17.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 17.31/17.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 17.31/17.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 17.31/17.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 17.31/17.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 17.31/17.49  thf(t38_funct_2, conjecture,
% 17.31/17.49    (![A:$i,B:$i,C:$i,D:$i]:
% 17.31/17.49     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 17.31/17.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 17.31/17.49       ( ( r1_tarski @ C @ A ) =>
% 17.31/17.49         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 17.31/17.49           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 17.31/17.49             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 17.31/17.49             ( m1_subset_1 @
% 17.31/17.49               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 17.31/17.49               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 17.31/17.49  thf(zf_stmt_0, negated_conjecture,
% 17.31/17.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 17.31/17.49        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 17.31/17.49            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 17.31/17.49          ( ( r1_tarski @ C @ A ) =>
% 17.31/17.49            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 17.31/17.49              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 17.31/17.49                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 17.31/17.49                ( m1_subset_1 @
% 17.31/17.49                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 17.31/17.49                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 17.31/17.49    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 17.31/17.49  thf('0', plain,
% 17.31/17.49      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 17.31/17.49        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 17.31/17.49             sk_B)
% 17.31/17.49        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 17.31/17.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 17.31/17.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.31/17.49  thf('1', plain,
% 17.31/17.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.31/17.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.31/17.49  thf(dt_k2_partfun1, axiom,
% 17.31/17.49    (![A:$i,B:$i,C:$i,D:$i]:
% 17.31/17.49     ( ( ( v1_funct_1 @ C ) & 
% 17.31/17.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 17.31/17.49       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 17.31/17.49         ( m1_subset_1 @
% 17.31/17.49           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 17.31/17.49           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 17.31/17.49  thf('2', plain,
% 17.31/17.49      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 17.31/17.49         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 17.31/17.49          | ~ (v1_funct_1 @ X39)
% 17.31/17.49          | (v1_funct_1 @ (k2_partfun1 @ X40 @ X41 @ X39 @ X42)))),
% 17.31/17.49      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 17.31/17.49  thf('3', plain,
% 17.31/17.49      (![X0 : $i]:
% 17.31/17.49         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 17.31/17.49          | ~ (v1_funct_1 @ sk_D))),
% 17.31/17.49      inference('sup-', [status(thm)], ['1', '2'])).
% 17.31/17.49  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 17.31/17.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.31/17.49  thf('5', plain,
% 17.31/17.49      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 17.31/17.49      inference('demod', [status(thm)], ['3', '4'])).
% 17.31/17.49  thf('6', plain,
% 17.31/17.49      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 17.31/17.49        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 17.31/17.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 17.31/17.49      inference('demod', [status(thm)], ['0', '5'])).
% 17.31/17.49  thf('7', plain,
% 17.31/17.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.31/17.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.31/17.49  thf(redefinition_k2_partfun1, axiom,
% 17.31/17.49    (![A:$i,B:$i,C:$i,D:$i]:
% 17.31/17.49     ( ( ( v1_funct_1 @ C ) & 
% 17.31/17.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 17.31/17.49       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 17.31/17.49  thf('8', plain,
% 17.31/17.49      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 17.31/17.49         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 17.31/17.49          | ~ (v1_funct_1 @ X43)
% 17.31/17.49          | ((k2_partfun1 @ X44 @ X45 @ X43 @ X46) = (k7_relat_1 @ X43 @ X46)))),
% 17.31/17.49      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 17.31/17.49  thf('9', plain,
% 17.31/17.49      (![X0 : $i]:
% 17.31/17.49         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 17.31/17.49          | ~ (v1_funct_1 @ sk_D))),
% 17.31/17.49      inference('sup-', [status(thm)], ['7', '8'])).
% 17.31/17.49  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 17.31/17.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.31/17.49  thf('11', plain,
% 17.31/17.49      (![X0 : $i]:
% 17.31/17.49         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 17.31/17.49      inference('demod', [status(thm)], ['9', '10'])).
% 17.31/17.49  thf('12', plain,
% 17.31/17.49      (![X0 : $i]:
% 17.31/17.49         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 17.31/17.49      inference('demod', [status(thm)], ['9', '10'])).
% 17.31/17.49  thf('13', plain,
% 17.31/17.49      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 17.31/17.49        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 17.31/17.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 17.31/17.49      inference('demod', [status(thm)], ['6', '11', '12'])).
% 17.31/17.49  thf('14', plain, ((r1_tarski @ sk_C @ sk_A)),
% 17.31/17.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.31/17.49  thf(d1_funct_2, axiom,
% 17.31/17.49    (![A:$i,B:$i,C:$i]:
% 17.31/17.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.31/17.49       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 17.31/17.49           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 17.31/17.49             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 17.31/17.49         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 17.31/17.49           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 17.31/17.49             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 17.31/17.49  thf(zf_stmt_1, axiom,
% 17.31/17.49    (![B:$i,A:$i]:
% 17.31/17.49     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 17.31/17.49       ( zip_tseitin_0 @ B @ A ) ))).
% 17.31/17.49  thf('15', plain,
% 17.31/17.49      (![X31 : $i, X32 : $i]:
% 17.31/17.49         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 17.31/17.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 17.31/17.49  thf('16', plain,
% 17.31/17.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.31/17.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.31/17.49  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 17.31/17.49  thf(zf_stmt_3, axiom,
% 17.31/17.49    (![C:$i,B:$i,A:$i]:
% 17.31/17.49     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 17.31/17.49       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 17.31/17.49  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 17.31/17.49  thf(zf_stmt_5, axiom,
% 17.31/17.49    (![A:$i,B:$i,C:$i]:
% 17.31/17.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.31/17.49       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 17.31/17.49         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 17.31/17.49           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 17.31/17.49             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 17.31/17.49  thf('17', plain,
% 17.31/17.49      (![X36 : $i, X37 : $i, X38 : $i]:
% 17.31/17.49         (~ (zip_tseitin_0 @ X36 @ X37)
% 17.31/17.49          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 17.31/17.49          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 17.31/17.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 17.31/17.49  thf('18', plain,
% 17.31/17.49      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 17.31/17.49      inference('sup-', [status(thm)], ['16', '17'])).
% 17.31/17.49  thf('19', plain,
% 17.31/17.49      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 17.31/17.49      inference('sup-', [status(thm)], ['15', '18'])).
% 17.31/17.49  thf('20', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 17.31/17.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.31/17.49  thf('21', plain,
% 17.31/17.49      (![X33 : $i, X34 : $i, X35 : $i]:
% 17.31/17.49         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 17.31/17.49          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 17.31/17.49          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 17.31/17.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 17.31/17.49  thf('22', plain,
% 17.31/17.49      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 17.31/17.49        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 17.31/17.49      inference('sup-', [status(thm)], ['20', '21'])).
% 17.31/17.49  thf('23', plain,
% 17.31/17.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.31/17.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.31/17.49  thf(redefinition_k1_relset_1, axiom,
% 17.31/17.49    (![A:$i,B:$i,C:$i]:
% 17.31/17.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.31/17.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 17.31/17.49  thf('24', plain,
% 17.31/17.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 17.31/17.49         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 17.31/17.49          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 17.31/17.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 17.31/17.49  thf('25', plain,
% 17.31/17.49      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 17.31/17.49      inference('sup-', [status(thm)], ['23', '24'])).
% 17.31/17.49  thf('26', plain,
% 17.31/17.49      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 17.31/17.49      inference('demod', [status(thm)], ['22', '25'])).
% 17.31/17.49  thf('27', plain,
% 17.31/17.49      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 17.31/17.49      inference('sup-', [status(thm)], ['19', '26'])).
% 17.31/17.49  thf('28', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 17.31/17.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.31/17.49  thf('29', plain,
% 17.31/17.49      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 17.31/17.49      inference('split', [status(esa)], ['28'])).
% 17.31/17.49  thf('30', plain,
% 17.31/17.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.49      inference('split', [status(esa)], ['28'])).
% 17.31/17.49  thf('31', plain,
% 17.31/17.49      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 17.31/17.49        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 17.31/17.50             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 17.31/17.50      inference('demod', [status(thm)], ['0', '5'])).
% 17.31/17.50  thf('32', plain,
% 17.31/17.50      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 17.31/17.50            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 17.31/17.50         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 17.31/17.50              sk_B)))
% 17.31/17.50         <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('sup-', [status(thm)], ['30', '31'])).
% 17.31/17.50  thf('33', plain,
% 17.31/17.50      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('split', [status(esa)], ['28'])).
% 17.31/17.50  thf('34', plain,
% 17.31/17.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.31/17.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.31/17.50  thf('35', plain,
% 17.31/17.50      (((m1_subset_1 @ sk_D @ 
% 17.31/17.50         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 17.31/17.50         <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('sup+', [status(thm)], ['33', '34'])).
% 17.31/17.50  thf(t113_zfmisc_1, axiom,
% 17.31/17.50    (![A:$i,B:$i]:
% 17.31/17.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 17.31/17.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 17.31/17.50  thf('36', plain,
% 17.31/17.50      (![X9 : $i, X10 : $i]:
% 17.31/17.50         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 17.31/17.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 17.31/17.50  thf('37', plain,
% 17.31/17.50      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 17.31/17.50      inference('simplify', [status(thm)], ['36'])).
% 17.31/17.50  thf('38', plain,
% 17.31/17.50      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 17.31/17.50         <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('demod', [status(thm)], ['35', '37'])).
% 17.31/17.50  thf(t3_subset, axiom,
% 17.31/17.50    (![A:$i,B:$i]:
% 17.31/17.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 17.31/17.50  thf('39', plain,
% 17.31/17.50      (![X11 : $i, X12 : $i]:
% 17.31/17.50         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 17.31/17.50      inference('cnf', [status(esa)], [t3_subset])).
% 17.31/17.50  thf('40', plain,
% 17.31/17.50      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('sup-', [status(thm)], ['38', '39'])).
% 17.31/17.50  thf(t3_xboole_1, axiom,
% 17.31/17.50    (![A:$i]:
% 17.31/17.50     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 17.31/17.50  thf('41', plain,
% 17.31/17.50      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 17.31/17.50      inference('cnf', [status(esa)], [t3_xboole_1])).
% 17.31/17.50  thf('42', plain,
% 17.31/17.50      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('sup-', [status(thm)], ['40', '41'])).
% 17.31/17.50  thf('43', plain,
% 17.31/17.50      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('split', [status(esa)], ['28'])).
% 17.31/17.50  thf('44', plain, ((r1_tarski @ sk_C @ sk_A)),
% 17.31/17.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.31/17.50  thf('45', plain,
% 17.31/17.50      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('sup+', [status(thm)], ['43', '44'])).
% 17.31/17.50  thf('46', plain,
% 17.31/17.50      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 17.31/17.50      inference('cnf', [status(esa)], [t3_xboole_1])).
% 17.31/17.50  thf('47', plain,
% 17.31/17.50      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('sup-', [status(thm)], ['45', '46'])).
% 17.31/17.50  thf('48', plain,
% 17.31/17.50      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('sup-', [status(thm)], ['40', '41'])).
% 17.31/17.50  thf('49', plain, ((v1_funct_1 @ sk_D)),
% 17.31/17.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.31/17.50  thf('50', plain,
% 17.31/17.50      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('sup+', [status(thm)], ['48', '49'])).
% 17.31/17.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 17.31/17.50  thf('51', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 17.31/17.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 17.31/17.50  thf('52', plain,
% 17.31/17.50      (![X11 : $i, X13 : $i]:
% 17.31/17.50         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 17.31/17.50      inference('cnf', [status(esa)], [t3_subset])).
% 17.31/17.50  thf('53', plain,
% 17.31/17.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 17.31/17.50      inference('sup-', [status(thm)], ['51', '52'])).
% 17.31/17.50  thf('54', plain,
% 17.31/17.50      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 17.31/17.50         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 17.31/17.50          | ~ (v1_funct_1 @ X43)
% 17.31/17.50          | ((k2_partfun1 @ X44 @ X45 @ X43 @ X46) = (k7_relat_1 @ X43 @ X46)))),
% 17.31/17.50      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 17.31/17.50  thf('55', plain,
% 17.31/17.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.31/17.50         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 17.31/17.50            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 17.31/17.50          | ~ (v1_funct_1 @ k1_xboole_0))),
% 17.31/17.50      inference('sup-', [status(thm)], ['53', '54'])).
% 17.31/17.50  thf(t88_relat_1, axiom,
% 17.31/17.50    (![A:$i,B:$i]:
% 17.31/17.50     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 17.31/17.50  thf('56', plain,
% 17.31/17.50      (![X18 : $i, X19 : $i]:
% 17.31/17.50         ((r1_tarski @ (k7_relat_1 @ X18 @ X19) @ X18) | ~ (v1_relat_1 @ X18))),
% 17.31/17.50      inference('cnf', [status(esa)], [t88_relat_1])).
% 17.31/17.50  thf('57', plain,
% 17.31/17.50      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 17.31/17.50      inference('cnf', [status(esa)], [t3_xboole_1])).
% 17.31/17.50  thf('58', plain,
% 17.31/17.50      (![X0 : $i]:
% 17.31/17.50         (~ (v1_relat_1 @ k1_xboole_0)
% 17.31/17.50          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 17.31/17.50      inference('sup-', [status(thm)], ['56', '57'])).
% 17.31/17.50  thf('59', plain,
% 17.31/17.50      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 17.31/17.50      inference('simplify', [status(thm)], ['36'])).
% 17.31/17.50  thf(fc6_relat_1, axiom,
% 17.31/17.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 17.31/17.50  thf('60', plain,
% 17.31/17.50      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 17.31/17.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 17.31/17.50  thf('61', plain, ((v1_relat_1 @ k1_xboole_0)),
% 17.31/17.50      inference('sup+', [status(thm)], ['59', '60'])).
% 17.31/17.50  thf('62', plain,
% 17.31/17.50      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 17.31/17.50      inference('demod', [status(thm)], ['58', '61'])).
% 17.31/17.50  thf('63', plain,
% 17.31/17.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.31/17.50         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 17.31/17.50          | ~ (v1_funct_1 @ k1_xboole_0))),
% 17.31/17.50      inference('demod', [status(thm)], ['55', '62'])).
% 17.31/17.50  thf('64', plain,
% 17.31/17.50      ((![X0 : $i, X1 : $i, X2 : $i]:
% 17.31/17.50          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 17.31/17.50         <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('sup-', [status(thm)], ['50', '63'])).
% 17.31/17.50  thf('65', plain,
% 17.31/17.50      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('sup-', [status(thm)], ['45', '46'])).
% 17.31/17.50  thf('66', plain,
% 17.31/17.50      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 17.31/17.50      inference('simplify', [status(thm)], ['36'])).
% 17.31/17.50  thf('67', plain,
% 17.31/17.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 17.31/17.50      inference('sup-', [status(thm)], ['51', '52'])).
% 17.31/17.50  thf('68', plain,
% 17.31/17.50      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('split', [status(esa)], ['28'])).
% 17.31/17.50  thf('69', plain,
% 17.31/17.50      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('sup-', [status(thm)], ['40', '41'])).
% 17.31/17.50  thf('70', plain,
% 17.31/17.50      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('sup-', [status(thm)], ['45', '46'])).
% 17.31/17.50  thf('71', plain,
% 17.31/17.50      ((![X0 : $i, X1 : $i, X2 : $i]:
% 17.31/17.50          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 17.31/17.50         <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('sup-', [status(thm)], ['50', '63'])).
% 17.31/17.50  thf('72', plain,
% 17.31/17.50      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.31/17.50      inference('sup-', [status(thm)], ['45', '46'])).
% 17.31/17.50  thf('73', plain,
% 17.31/17.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 17.31/17.50      inference('sup-', [status(thm)], ['51', '52'])).
% 17.31/17.50  thf('74', plain,
% 17.31/17.50      (![X28 : $i, X29 : $i, X30 : $i]:
% 17.31/17.50         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 17.31/17.50          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 17.31/17.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 17.31/17.50  thf('75', plain,
% 17.31/17.50      (![X0 : $i, X1 : $i]:
% 17.31/17.50         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 17.31/17.50      inference('sup-', [status(thm)], ['73', '74'])).
% 17.31/17.50  thf('76', plain,
% 17.31/17.50      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 17.31/17.50      inference('demod', [status(thm)], ['58', '61'])).
% 17.31/17.50  thf('77', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 17.31/17.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 17.31/17.50  thf(t91_relat_1, axiom,
% 17.31/17.50    (![A:$i,B:$i]:
% 17.31/17.50     ( ( v1_relat_1 @ B ) =>
% 17.31/17.50       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 17.31/17.50         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 17.31/17.50  thf('78', plain,
% 17.31/17.50      (![X20 : $i, X21 : $i]:
% 17.31/17.50         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 17.31/17.50          | ((k1_relat_1 @ (k7_relat_1 @ X21 @ X20)) = (X20))
% 17.31/17.50          | ~ (v1_relat_1 @ X21))),
% 17.31/17.50      inference('cnf', [status(esa)], [t91_relat_1])).
% 17.31/17.50  thf('79', plain,
% 17.31/17.50      (![X0 : $i]:
% 17.31/17.50         (~ (v1_relat_1 @ X0)
% 17.31/17.50          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 17.31/17.50      inference('sup-', [status(thm)], ['77', '78'])).
% 17.31/17.50  thf('80', plain,
% 17.31/17.50      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 17.31/17.50        | ~ (v1_relat_1 @ k1_xboole_0))),
% 17.31/17.50      inference('sup+', [status(thm)], ['76', '79'])).
% 17.31/17.50  thf('81', plain, ((v1_relat_1 @ k1_xboole_0)),
% 17.31/17.50      inference('sup+', [status(thm)], ['59', '60'])).
% 17.31/17.50  thf('82', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 17.31/17.50      inference('demod', [status(thm)], ['80', '81'])).
% 17.31/17.50  thf('83', plain,
% 17.31/17.50      (![X0 : $i, X1 : $i]:
% 17.31/17.50         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 17.31/17.50      inference('demod', [status(thm)], ['75', '82'])).
% 17.31/17.50  thf('84', plain,
% 17.31/17.50      (![X33 : $i, X34 : $i, X35 : $i]:
% 17.31/17.50         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 17.31/17.50          | (v1_funct_2 @ X35 @ X33 @ X34)
% 17.31/17.50          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 17.31/17.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 17.31/17.50  thf('85', plain,
% 17.31/17.50      (![X0 : $i, X1 : $i]:
% 17.31/17.50         (((X1) != (k1_xboole_0))
% 17.31/17.50          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 17.31/17.50          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 17.31/17.50      inference('sup-', [status(thm)], ['83', '84'])).
% 17.31/17.50  thf('86', plain,
% 17.31/17.50      (![X0 : $i]:
% 17.31/17.50         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 17.31/17.50          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 17.31/17.50      inference('simplify', [status(thm)], ['85'])).
% 17.31/17.50  thf('87', plain,
% 17.31/17.50      (![X31 : $i, X32 : $i]:
% 17.31/17.50         ((zip_tseitin_0 @ X31 @ X32) | ((X32) != (k1_xboole_0)))),
% 17.31/17.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 17.31/17.50  thf('88', plain, (![X31 : $i]: (zip_tseitin_0 @ X31 @ k1_xboole_0)),
% 17.31/17.50      inference('simplify', [status(thm)], ['87'])).
% 17.31/17.50  thf('89', plain,
% 17.31/17.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 17.31/17.50      inference('sup-', [status(thm)], ['51', '52'])).
% 17.31/17.50  thf('90', plain,
% 17.31/17.50      (![X36 : $i, X37 : $i, X38 : $i]:
% 17.31/17.50         (~ (zip_tseitin_0 @ X36 @ X37)
% 17.31/17.50          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 17.31/17.50          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 17.31/17.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 17.31/17.50  thf('91', plain,
% 17.31/17.50      (![X0 : $i, X1 : $i]:
% 17.31/17.50         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 17.31/17.50      inference('sup-', [status(thm)], ['89', '90'])).
% 17.31/17.50  thf('92', plain,
% 17.31/17.50      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 17.31/17.50      inference('sup-', [status(thm)], ['88', '91'])).
% 17.31/17.50  thf('93', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 17.31/17.50      inference('demod', [status(thm)], ['86', '92'])).
% 17.31/17.50  thf('94', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 17.31/17.50      inference('demod', [status(thm)],
% 17.31/17.50                ['32', '42', '47', '64', '65', '66', '67', '68', '69', '70', 
% 17.31/17.50                 '71', '72', '93'])).
% 17.31/17.50  thf('95', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 17.31/17.50      inference('split', [status(esa)], ['28'])).
% 17.31/17.50  thf('96', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 17.31/17.50      inference('sat_resolution*', [status(thm)], ['94', '95'])).
% 17.31/17.50  thf('97', plain, (((sk_B) != (k1_xboole_0))),
% 17.31/17.50      inference('simpl_trail', [status(thm)], ['29', '96'])).
% 17.31/17.50  thf('98', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 17.31/17.50      inference('simplify_reflect-', [status(thm)], ['27', '97'])).
% 17.31/17.50  thf('99', plain,
% 17.31/17.50      (![X20 : $i, X21 : $i]:
% 17.31/17.50         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 17.31/17.50          | ((k1_relat_1 @ (k7_relat_1 @ X21 @ X20)) = (X20))
% 17.31/17.50          | ~ (v1_relat_1 @ X21))),
% 17.31/17.50      inference('cnf', [status(esa)], [t91_relat_1])).
% 17.31/17.50  thf('100', plain,
% 17.31/17.50      (![X0 : $i]:
% 17.31/17.50         (~ (r1_tarski @ X0 @ sk_A)
% 17.31/17.50          | ~ (v1_relat_1 @ sk_D)
% 17.31/17.50          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 17.31/17.50      inference('sup-', [status(thm)], ['98', '99'])).
% 17.31/17.50  thf('101', plain,
% 17.31/17.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.31/17.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.31/17.50  thf(cc1_relset_1, axiom,
% 17.31/17.50    (![A:$i,B:$i,C:$i]:
% 17.31/17.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.31/17.50       ( v1_relat_1 @ C ) ))).
% 17.31/17.50  thf('102', plain,
% 17.31/17.50      (![X22 : $i, X23 : $i, X24 : $i]:
% 17.31/17.50         ((v1_relat_1 @ X22)
% 17.31/17.50          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 17.31/17.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 17.31/17.50  thf('103', plain, ((v1_relat_1 @ sk_D)),
% 17.31/17.50      inference('sup-', [status(thm)], ['101', '102'])).
% 17.31/17.50  thf('104', plain,
% 17.31/17.50      (![X0 : $i]:
% 17.31/17.50         (~ (r1_tarski @ X0 @ sk_A)
% 17.31/17.50          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 17.31/17.50      inference('demod', [status(thm)], ['100', '103'])).
% 17.31/17.50  thf('105', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 17.31/17.50      inference('sup-', [status(thm)], ['14', '104'])).
% 17.31/17.50  thf('106', plain,
% 17.31/17.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.31/17.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.31/17.50  thf('107', plain,
% 17.31/17.50      (![X11 : $i, X12 : $i]:
% 17.31/17.50         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 17.31/17.50      inference('cnf', [status(esa)], [t3_subset])).
% 17.31/17.50  thf('108', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 17.31/17.50      inference('sup-', [status(thm)], ['106', '107'])).
% 17.31/17.50  thf('109', plain,
% 17.31/17.50      (![X18 : $i, X19 : $i]:
% 17.31/17.50         ((r1_tarski @ (k7_relat_1 @ X18 @ X19) @ X18) | ~ (v1_relat_1 @ X18))),
% 17.31/17.50      inference('cnf', [status(esa)], [t88_relat_1])).
% 17.31/17.50  thf(t1_xboole_1, axiom,
% 17.31/17.50    (![A:$i,B:$i,C:$i]:
% 17.31/17.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 17.31/17.50       ( r1_tarski @ A @ C ) ))).
% 17.31/17.50  thf('110', plain,
% 17.31/17.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 17.31/17.50         (~ (r1_tarski @ X3 @ X4)
% 17.31/17.50          | ~ (r1_tarski @ X4 @ X5)
% 17.31/17.50          | (r1_tarski @ X3 @ X5))),
% 17.31/17.50      inference('cnf', [status(esa)], [t1_xboole_1])).
% 17.31/17.50  thf('111', plain,
% 17.31/17.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.31/17.50         (~ (v1_relat_1 @ X0)
% 17.31/17.50          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 17.31/17.50          | ~ (r1_tarski @ X0 @ X2))),
% 17.31/17.50      inference('sup-', [status(thm)], ['109', '110'])).
% 17.31/17.50  thf('112', plain,
% 17.31/17.50      (![X0 : $i]:
% 17.31/17.50         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 17.31/17.50          | ~ (v1_relat_1 @ sk_D))),
% 17.31/17.50      inference('sup-', [status(thm)], ['108', '111'])).
% 17.31/17.50  thf('113', plain, ((v1_relat_1 @ sk_D)),
% 17.31/17.50      inference('sup-', [status(thm)], ['101', '102'])).
% 17.31/17.50  thf('114', plain,
% 17.31/17.50      (![X0 : $i]:
% 17.31/17.50         (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 17.31/17.50      inference('demod', [status(thm)], ['112', '113'])).
% 17.31/17.50  thf('115', plain,
% 17.31/17.50      (![X11 : $i, X13 : $i]:
% 17.31/17.50         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 17.31/17.50      inference('cnf', [status(esa)], [t3_subset])).
% 17.31/17.50  thf('116', plain,
% 17.31/17.50      (![X0 : $i]:
% 17.31/17.50         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 17.31/17.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.31/17.50      inference('sup-', [status(thm)], ['114', '115'])).
% 17.31/17.50  thf(cc2_relset_1, axiom,
% 17.31/17.50    (![A:$i,B:$i,C:$i]:
% 17.31/17.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.31/17.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 17.31/17.50  thf('117', plain,
% 17.31/17.50      (![X25 : $i, X26 : $i, X27 : $i]:
% 17.31/17.50         ((v5_relat_1 @ X25 @ X27)
% 17.31/17.50          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 17.31/17.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 17.31/17.50  thf('118', plain,
% 17.31/17.50      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 17.31/17.50      inference('sup-', [status(thm)], ['116', '117'])).
% 17.31/17.50  thf(d19_relat_1, axiom,
% 17.31/17.50    (![A:$i,B:$i]:
% 17.31/17.50     ( ( v1_relat_1 @ B ) =>
% 17.31/17.50       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 17.31/17.50  thf('119', plain,
% 17.31/17.50      (![X14 : $i, X15 : $i]:
% 17.31/17.50         (~ (v5_relat_1 @ X14 @ X15)
% 17.31/17.50          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 17.31/17.50          | ~ (v1_relat_1 @ X14))),
% 17.31/17.50      inference('cnf', [status(esa)], [d19_relat_1])).
% 17.31/17.50  thf('120', plain,
% 17.31/17.50      (![X0 : $i]:
% 17.31/17.50         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 17.31/17.50          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 17.31/17.50      inference('sup-', [status(thm)], ['118', '119'])).
% 17.31/17.50  thf('121', plain,
% 17.31/17.50      (![X0 : $i]:
% 17.31/17.50         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 17.31/17.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.31/17.50      inference('sup-', [status(thm)], ['114', '115'])).
% 17.31/17.50  thf('122', plain,
% 17.31/17.50      (![X22 : $i, X23 : $i, X24 : $i]:
% 17.31/17.50         ((v1_relat_1 @ X22)
% 17.31/17.50          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 17.31/17.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 17.31/17.50  thf('123', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 17.31/17.50      inference('sup-', [status(thm)], ['121', '122'])).
% 17.31/17.50  thf('124', plain,
% 17.31/17.50      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 17.31/17.50      inference('demod', [status(thm)], ['120', '123'])).
% 17.31/17.50  thf(t4_funct_2, axiom,
% 17.31/17.50    (![A:$i,B:$i]:
% 17.31/17.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 17.31/17.50       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 17.31/17.50         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 17.31/17.50           ( m1_subset_1 @
% 17.31/17.50             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 17.31/17.50  thf('125', plain,
% 17.31/17.50      (![X47 : $i, X48 : $i]:
% 17.31/17.50         (~ (r1_tarski @ (k2_relat_1 @ X47) @ X48)
% 17.31/17.50          | (v1_funct_2 @ X47 @ (k1_relat_1 @ X47) @ X48)
% 17.31/17.50          | ~ (v1_funct_1 @ X47)
% 17.31/17.50          | ~ (v1_relat_1 @ X47))),
% 17.31/17.50      inference('cnf', [status(esa)], [t4_funct_2])).
% 17.31/17.50  thf('126', plain,
% 17.31/17.50      (![X0 : $i]:
% 17.31/17.50         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 17.31/17.50          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 17.31/17.50          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 17.31/17.50             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 17.31/17.50      inference('sup-', [status(thm)], ['124', '125'])).
% 17.31/17.50  thf('127', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 17.31/17.50      inference('sup-', [status(thm)], ['121', '122'])).
% 17.31/17.50  thf('128', plain,
% 17.31/17.50      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 17.31/17.50      inference('demod', [status(thm)], ['3', '4'])).
% 17.31/17.50  thf('129', plain,
% 17.31/17.50      (![X0 : $i]:
% 17.31/17.50         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 17.31/17.50      inference('demod', [status(thm)], ['9', '10'])).
% 17.31/17.50  thf('130', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 17.31/17.50      inference('demod', [status(thm)], ['128', '129'])).
% 17.31/17.50  thf('131', plain,
% 17.31/17.50      (![X0 : $i]:
% 17.31/17.50         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 17.31/17.50          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 17.31/17.50      inference('demod', [status(thm)], ['126', '127', '130'])).
% 17.31/17.50  thf('132', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 17.31/17.50      inference('sup+', [status(thm)], ['105', '131'])).
% 17.31/17.50  thf('133', plain,
% 17.31/17.50      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 17.31/17.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 17.31/17.50      inference('demod', [status(thm)], ['13', '132'])).
% 17.31/17.50  thf('134', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 17.31/17.50      inference('sup-', [status(thm)], ['14', '104'])).
% 17.31/17.50  thf('135', plain,
% 17.31/17.50      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 17.31/17.50      inference('demod', [status(thm)], ['120', '123'])).
% 17.31/17.50  thf('136', plain,
% 17.31/17.50      (![X47 : $i, X48 : $i]:
% 17.31/17.50         (~ (r1_tarski @ (k2_relat_1 @ X47) @ X48)
% 17.31/17.50          | (m1_subset_1 @ X47 @ 
% 17.31/17.50             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X47) @ X48)))
% 17.31/17.50          | ~ (v1_funct_1 @ X47)
% 17.31/17.50          | ~ (v1_relat_1 @ X47))),
% 17.31/17.50      inference('cnf', [status(esa)], [t4_funct_2])).
% 17.31/17.50  thf('137', plain,
% 17.31/17.50      (![X0 : $i]:
% 17.31/17.50         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 17.31/17.50          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 17.31/17.50          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 17.31/17.50             (k1_zfmisc_1 @ 
% 17.31/17.50              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 17.31/17.50      inference('sup-', [status(thm)], ['135', '136'])).
% 17.31/17.50  thf('138', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 17.31/17.50      inference('sup-', [status(thm)], ['121', '122'])).
% 17.31/17.50  thf('139', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 17.31/17.50      inference('demod', [status(thm)], ['128', '129'])).
% 17.31/17.50  thf('140', plain,
% 17.31/17.50      (![X0 : $i]:
% 17.31/17.50         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 17.31/17.50          (k1_zfmisc_1 @ 
% 17.31/17.50           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 17.31/17.50      inference('demod', [status(thm)], ['137', '138', '139'])).
% 17.31/17.50  thf('141', plain,
% 17.31/17.50      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 17.31/17.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 17.31/17.50      inference('sup+', [status(thm)], ['134', '140'])).
% 17.31/17.50  thf('142', plain, ($false), inference('demod', [status(thm)], ['133', '141'])).
% 17.31/17.50  
% 17.31/17.50  % SZS output end Refutation
% 17.31/17.50  
% 17.31/17.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
