%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TFbtd9unCr

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:11 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 556 expanded)
%              Number of leaves         :   44 ( 177 expanded)
%              Depth                    :   18
%              Number of atoms          :  997 (7489 expanded)
%              Number of equality atoms :   74 ( 437 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
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

thf('5',plain,(
    ! [X44: $i,X45: $i] :
      ( ( zip_tseitin_0 @ X44 @ X45 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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

thf('7',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( zip_tseitin_0 @ X49 @ X50 )
      | ( zip_tseitin_1 @ X51 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_2 @ X48 @ X46 @ X47 )
      | ( X46
        = ( k1_relset_1 @ X46 @ X47 @ X48 ) )
      | ~ ( zip_tseitin_1 @ X48 @ X47 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X37 )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    r1_tarski @ sk_B_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v5_relat_1 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v5_relat_1 @ sk_D @ sk_B_2 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v5_relat_1 @ X22 @ X23 )
      | ( r1_tarski @ ( k2_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B_2 ),
    inference(demod,[status(thm)],['23','26'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['18','29'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X52 ) @ X53 )
      | ( v1_funct_2 @ X52 @ ( k1_relat_1 @ X52 ) @ X53 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','35'])).

thf('37',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('44',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('48',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ sk_D @ X0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D ) )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('56',plain,
    ( ( v4_relat_1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('57',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('58',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('60',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('61',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('64',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['67'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('69',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['51','66','72'])).

thf('74',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('75',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['4','42','73','74','75'])).

thf('77',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','76'])).

thf('78',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('79',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['18','29'])).

thf('80',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X52 ) @ X53 )
      | ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X52 ) @ X53 ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('83',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('86',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','86'])).

thf('88',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('91',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('92',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('93',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','71'])).

thf('98',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','42','73','75','98','74'])).

thf('100',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['88','99'])).

thf('101',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['87','100'])).

thf('102',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('103',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['77','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TFbtd9unCr
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:12:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.15/1.33  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.15/1.33  % Solved by: fo/fo7.sh
% 1.15/1.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.33  % done 1350 iterations in 0.873s
% 1.15/1.33  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.15/1.33  % SZS output start Refutation
% 1.15/1.33  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.33  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.15/1.33  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.15/1.33  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.15/1.33  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.15/1.33  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.15/1.33  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.15/1.33  thf(sk_C_type, type, sk_C: $i).
% 1.15/1.33  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.15/1.33  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.15/1.33  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.15/1.33  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.15/1.33  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.15/1.33  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.15/1.33  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.15/1.33  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.15/1.33  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.15/1.33  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.15/1.33  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.15/1.33  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.15/1.33  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.15/1.33  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.15/1.33  thf(sk_D_type, type, sk_D: $i).
% 1.15/1.33  thf(t9_funct_2, conjecture,
% 1.15/1.33    (![A:$i,B:$i,C:$i,D:$i]:
% 1.15/1.33     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.15/1.33         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.15/1.33       ( ( r1_tarski @ B @ C ) =>
% 1.15/1.33         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.15/1.33           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.15/1.33             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 1.15/1.33  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.33    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.15/1.33        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.15/1.33            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.15/1.33          ( ( r1_tarski @ B @ C ) =>
% 1.15/1.33            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.15/1.33              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.15/1.33                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 1.15/1.33    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 1.15/1.33  thf('0', plain,
% 1.15/1.33      ((~ (v1_funct_1 @ sk_D)
% 1.15/1.33        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 1.15/1.33        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf('1', plain,
% 1.15/1.33      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 1.15/1.33         <= (~
% 1.15/1.33             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 1.15/1.33      inference('split', [status(esa)], ['0'])).
% 1.15/1.33  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 1.15/1.33      inference('split', [status(esa)], ['0'])).
% 1.15/1.33  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 1.15/1.33      inference('sup-', [status(thm)], ['2', '3'])).
% 1.15/1.33  thf(d1_funct_2, axiom,
% 1.15/1.33    (![A:$i,B:$i,C:$i]:
% 1.15/1.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.33       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.15/1.33           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.15/1.33             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.15/1.33         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.15/1.33           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.15/1.33             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.15/1.33  thf(zf_stmt_1, axiom,
% 1.15/1.33    (![B:$i,A:$i]:
% 1.15/1.33     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.15/1.33       ( zip_tseitin_0 @ B @ A ) ))).
% 1.15/1.33  thf('5', plain,
% 1.15/1.33      (![X44 : $i, X45 : $i]:
% 1.15/1.33         ((zip_tseitin_0 @ X44 @ X45) | ((X44) = (k1_xboole_0)))),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.15/1.33  thf('6', plain,
% 1.15/1.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.15/1.33  thf(zf_stmt_3, axiom,
% 1.15/1.33    (![C:$i,B:$i,A:$i]:
% 1.15/1.33     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.15/1.33       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.15/1.33  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.15/1.33  thf(zf_stmt_5, axiom,
% 1.15/1.33    (![A:$i,B:$i,C:$i]:
% 1.15/1.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.33       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.15/1.33         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.15/1.33           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.15/1.33             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.15/1.33  thf('7', plain,
% 1.15/1.33      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.15/1.33         (~ (zip_tseitin_0 @ X49 @ X50)
% 1.15/1.33          | (zip_tseitin_1 @ X51 @ X49 @ X50)
% 1.15/1.33          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49))))),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.15/1.33  thf('8', plain,
% 1.15/1.33      (((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 1.15/1.33        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 1.15/1.33      inference('sup-', [status(thm)], ['6', '7'])).
% 1.15/1.33  thf('9', plain,
% 1.15/1.33      ((((sk_B_2) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A))),
% 1.15/1.33      inference('sup-', [status(thm)], ['5', '8'])).
% 1.15/1.33  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_2)),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf('11', plain,
% 1.15/1.33      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.15/1.33         (~ (v1_funct_2 @ X48 @ X46 @ X47)
% 1.15/1.33          | ((X46) = (k1_relset_1 @ X46 @ X47 @ X48))
% 1.15/1.33          | ~ (zip_tseitin_1 @ X48 @ X47 @ X46))),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.15/1.33  thf('12', plain,
% 1.15/1.33      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 1.15/1.33        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_2 @ sk_D)))),
% 1.15/1.33      inference('sup-', [status(thm)], ['10', '11'])).
% 1.15/1.33  thf('13', plain,
% 1.15/1.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf(redefinition_k1_relset_1, axiom,
% 1.15/1.33    (![A:$i,B:$i,C:$i]:
% 1.15/1.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.33       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.15/1.33  thf('14', plain,
% 1.15/1.33      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.15/1.33         (((k1_relset_1 @ X38 @ X39 @ X37) = (k1_relat_1 @ X37))
% 1.15/1.33          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 1.15/1.33      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.15/1.33  thf('15', plain,
% 1.15/1.33      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.15/1.33      inference('sup-', [status(thm)], ['13', '14'])).
% 1.15/1.33  thf('16', plain,
% 1.15/1.33      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 1.15/1.33        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.15/1.33      inference('demod', [status(thm)], ['12', '15'])).
% 1.15/1.33  thf('17', plain,
% 1.15/1.33      ((((sk_B_2) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.15/1.33      inference('sup-', [status(thm)], ['9', '16'])).
% 1.15/1.33  thf('18', plain, ((r1_tarski @ sk_B_2 @ sk_C)),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf('19', plain,
% 1.15/1.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf(cc2_relset_1, axiom,
% 1.15/1.33    (![A:$i,B:$i,C:$i]:
% 1.15/1.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.33       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.15/1.33  thf('20', plain,
% 1.15/1.33      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.15/1.33         ((v5_relat_1 @ X31 @ X33)
% 1.15/1.33          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.15/1.33      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.15/1.33  thf('21', plain, ((v5_relat_1 @ sk_D @ sk_B_2)),
% 1.15/1.33      inference('sup-', [status(thm)], ['19', '20'])).
% 1.15/1.33  thf(d19_relat_1, axiom,
% 1.15/1.33    (![A:$i,B:$i]:
% 1.15/1.33     ( ( v1_relat_1 @ B ) =>
% 1.15/1.33       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.15/1.33  thf('22', plain,
% 1.15/1.33      (![X22 : $i, X23 : $i]:
% 1.15/1.33         (~ (v5_relat_1 @ X22 @ X23)
% 1.15/1.33          | (r1_tarski @ (k2_relat_1 @ X22) @ X23)
% 1.15/1.33          | ~ (v1_relat_1 @ X22))),
% 1.15/1.33      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.15/1.33  thf('23', plain,
% 1.15/1.33      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B_2))),
% 1.15/1.33      inference('sup-', [status(thm)], ['21', '22'])).
% 1.15/1.33  thf('24', plain,
% 1.15/1.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf(cc1_relset_1, axiom,
% 1.15/1.33    (![A:$i,B:$i,C:$i]:
% 1.15/1.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.33       ( v1_relat_1 @ C ) ))).
% 1.15/1.33  thf('25', plain,
% 1.15/1.33      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.15/1.33         ((v1_relat_1 @ X28)
% 1.15/1.33          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.15/1.33      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.15/1.33  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 1.15/1.33      inference('sup-', [status(thm)], ['24', '25'])).
% 1.15/1.33  thf('27', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B_2)),
% 1.15/1.33      inference('demod', [status(thm)], ['23', '26'])).
% 1.15/1.33  thf(t1_xboole_1, axiom,
% 1.15/1.33    (![A:$i,B:$i,C:$i]:
% 1.15/1.33     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.15/1.33       ( r1_tarski @ A @ C ) ))).
% 1.15/1.33  thf('28', plain,
% 1.15/1.33      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.15/1.33         (~ (r1_tarski @ X7 @ X8)
% 1.15/1.33          | ~ (r1_tarski @ X8 @ X9)
% 1.15/1.33          | (r1_tarski @ X7 @ X9))),
% 1.15/1.33      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.15/1.33  thf('29', plain,
% 1.15/1.33      (![X0 : $i]:
% 1.15/1.33         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0) | ~ (r1_tarski @ sk_B_2 @ X0))),
% 1.15/1.33      inference('sup-', [status(thm)], ['27', '28'])).
% 1.15/1.33  thf('30', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 1.15/1.33      inference('sup-', [status(thm)], ['18', '29'])).
% 1.15/1.33  thf(t4_funct_2, axiom,
% 1.15/1.33    (![A:$i,B:$i]:
% 1.15/1.33     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.15/1.33       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.15/1.33         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 1.15/1.33           ( m1_subset_1 @
% 1.15/1.33             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 1.15/1.33  thf('31', plain,
% 1.15/1.33      (![X52 : $i, X53 : $i]:
% 1.15/1.33         (~ (r1_tarski @ (k2_relat_1 @ X52) @ X53)
% 1.15/1.33          | (v1_funct_2 @ X52 @ (k1_relat_1 @ X52) @ X53)
% 1.15/1.33          | ~ (v1_funct_1 @ X52)
% 1.15/1.33          | ~ (v1_relat_1 @ X52))),
% 1.15/1.33      inference('cnf', [status(esa)], [t4_funct_2])).
% 1.15/1.33  thf('32', plain,
% 1.15/1.33      ((~ (v1_relat_1 @ sk_D)
% 1.15/1.33        | ~ (v1_funct_1 @ sk_D)
% 1.15/1.33        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C))),
% 1.15/1.33      inference('sup-', [status(thm)], ['30', '31'])).
% 1.15/1.33  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 1.15/1.33      inference('sup-', [status(thm)], ['24', '25'])).
% 1.15/1.33  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf('35', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C)),
% 1.15/1.33      inference('demod', [status(thm)], ['32', '33', '34'])).
% 1.15/1.33  thf('36', plain,
% 1.15/1.33      (((v1_funct_2 @ sk_D @ sk_A @ sk_C) | ((sk_B_2) = (k1_xboole_0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['17', '35'])).
% 1.15/1.33  thf('37', plain,
% 1.15/1.33      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 1.15/1.33         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.15/1.33      inference('split', [status(esa)], ['0'])).
% 1.15/1.33  thf('38', plain,
% 1.15/1.33      ((((sk_B_2) = (k1_xboole_0))) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.15/1.33      inference('sup-', [status(thm)], ['36', '37'])).
% 1.15/1.33  thf('39', plain, ((((sk_B_2) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf('40', plain,
% 1.15/1.33      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 1.15/1.33      inference('split', [status(esa)], ['39'])).
% 1.15/1.33  thf('41', plain,
% 1.15/1.33      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.15/1.33         <= (~ (((sk_B_2) = (k1_xboole_0))) & 
% 1.15/1.33             ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.15/1.33      inference('sup-', [status(thm)], ['38', '40'])).
% 1.15/1.33  thf('42', plain,
% 1.15/1.33      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | (((sk_B_2) = (k1_xboole_0)))),
% 1.15/1.33      inference('simplify', [status(thm)], ['41'])).
% 1.15/1.33  thf('43', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C)),
% 1.15/1.33      inference('demod', [status(thm)], ['32', '33', '34'])).
% 1.15/1.33  thf(t7_xboole_0, axiom,
% 1.15/1.33    (![A:$i]:
% 1.15/1.33     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.15/1.33          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.15/1.33  thf('44', plain,
% 1.15/1.33      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 1.15/1.33      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.15/1.33  thf(d1_xboole_0, axiom,
% 1.15/1.33    (![A:$i]:
% 1.15/1.33     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.15/1.33  thf('45', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.15/1.33      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.15/1.33  thf('46', plain,
% 1.15/1.33      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.15/1.33      inference('sup-', [status(thm)], ['44', '45'])).
% 1.15/1.33  thf('47', plain,
% 1.15/1.33      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.15/1.33      inference('split', [status(esa)], ['39'])).
% 1.15/1.33  thf('48', plain,
% 1.15/1.33      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 1.15/1.33         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.15/1.33      inference('split', [status(esa)], ['0'])).
% 1.15/1.33  thf('49', plain,
% 1.15/1.33      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 1.15/1.33         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 1.15/1.33      inference('sup-', [status(thm)], ['47', '48'])).
% 1.15/1.33  thf('50', plain,
% 1.15/1.33      ((![X0 : $i]: (~ (v1_funct_2 @ sk_D @ X0 @ sk_C) | ~ (v1_xboole_0 @ X0)))
% 1.15/1.33         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 1.15/1.33      inference('sup-', [status(thm)], ['46', '49'])).
% 1.15/1.33  thf('51', plain,
% 1.15/1.33      ((~ (v1_xboole_0 @ (k1_relat_1 @ sk_D)))
% 1.15/1.33         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 1.15/1.33      inference('sup-', [status(thm)], ['43', '50'])).
% 1.15/1.33  thf('52', plain,
% 1.15/1.33      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.15/1.33      inference('split', [status(esa)], ['39'])).
% 1.15/1.33  thf('53', plain,
% 1.15/1.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf('54', plain,
% 1.15/1.33      (((m1_subset_1 @ sk_D @ 
% 1.15/1.33         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2))))
% 1.15/1.33         <= ((((sk_A) = (k1_xboole_0))))),
% 1.15/1.33      inference('sup+', [status(thm)], ['52', '53'])).
% 1.15/1.33  thf('55', plain,
% 1.15/1.33      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.15/1.33         ((v4_relat_1 @ X31 @ X32)
% 1.15/1.33          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.15/1.33      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.15/1.33  thf('56', plain,
% 1.15/1.33      (((v4_relat_1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.15/1.33      inference('sup-', [status(thm)], ['54', '55'])).
% 1.15/1.33  thf(d18_relat_1, axiom,
% 1.15/1.33    (![A:$i,B:$i]:
% 1.15/1.33     ( ( v1_relat_1 @ B ) =>
% 1.15/1.33       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.15/1.33  thf('57', plain,
% 1.15/1.33      (![X20 : $i, X21 : $i]:
% 1.15/1.33         (~ (v4_relat_1 @ X20 @ X21)
% 1.15/1.33          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 1.15/1.33          | ~ (v1_relat_1 @ X20))),
% 1.15/1.33      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.15/1.33  thf('58', plain,
% 1.15/1.33      (((~ (v1_relat_1 @ sk_D)
% 1.15/1.33         | (r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0)))
% 1.15/1.33         <= ((((sk_A) = (k1_xboole_0))))),
% 1.15/1.33      inference('sup-', [status(thm)], ['56', '57'])).
% 1.15/1.33  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 1.15/1.33      inference('sup-', [status(thm)], ['24', '25'])).
% 1.15/1.33  thf('60', plain,
% 1.15/1.33      (((r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0))
% 1.15/1.33         <= ((((sk_A) = (k1_xboole_0))))),
% 1.15/1.33      inference('demod', [status(thm)], ['58', '59'])).
% 1.15/1.33  thf(t4_subset_1, axiom,
% 1.15/1.33    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.15/1.33  thf('61', plain,
% 1.15/1.33      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 1.15/1.33      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.15/1.33  thf(t3_subset, axiom,
% 1.15/1.33    (![A:$i,B:$i]:
% 1.15/1.33     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.15/1.33  thf('62', plain,
% 1.15/1.33      (![X14 : $i, X15 : $i]:
% 1.15/1.33         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.15/1.33      inference('cnf', [status(esa)], [t3_subset])).
% 1.15/1.33  thf('63', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.15/1.33      inference('sup-', [status(thm)], ['61', '62'])).
% 1.15/1.33  thf(d10_xboole_0, axiom,
% 1.15/1.33    (![A:$i,B:$i]:
% 1.15/1.33     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.15/1.33  thf('64', plain,
% 1.15/1.33      (![X4 : $i, X6 : $i]:
% 1.15/1.33         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.15/1.33      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.15/1.33  thf('65', plain,
% 1.15/1.33      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.15/1.33      inference('sup-', [status(thm)], ['63', '64'])).
% 1.15/1.33  thf('66', plain,
% 1.15/1.33      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.15/1.33      inference('sup-', [status(thm)], ['60', '65'])).
% 1.15/1.33  thf('67', plain,
% 1.15/1.33      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.15/1.33      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.15/1.33  thf('68', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.15/1.33      inference('simplify', [status(thm)], ['67'])).
% 1.15/1.33  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.15/1.33  thf('69', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 1.15/1.33      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.15/1.33  thf(t69_xboole_1, axiom,
% 1.15/1.33    (![A:$i,B:$i]:
% 1.15/1.33     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.15/1.33       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 1.15/1.33  thf('70', plain,
% 1.15/1.33      (![X11 : $i, X12 : $i]:
% 1.15/1.33         (~ (r1_xboole_0 @ X11 @ X12)
% 1.15/1.33          | ~ (r1_tarski @ X11 @ X12)
% 1.15/1.33          | (v1_xboole_0 @ X11))),
% 1.15/1.33      inference('cnf', [status(esa)], [t69_xboole_1])).
% 1.15/1.33  thf('71', plain,
% 1.15/1.33      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 1.15/1.33      inference('sup-', [status(thm)], ['69', '70'])).
% 1.15/1.33  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.33      inference('sup-', [status(thm)], ['68', '71'])).
% 1.15/1.33  thf('73', plain,
% 1.15/1.33      (~ (((sk_A) = (k1_xboole_0))) | ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 1.15/1.33      inference('demod', [status(thm)], ['51', '66', '72'])).
% 1.15/1.33  thf('74', plain,
% 1.15/1.33      (~ (((sk_B_2) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.15/1.33      inference('split', [status(esa)], ['39'])).
% 1.15/1.33  thf('75', plain,
% 1.15/1.33      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 1.15/1.33       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 1.15/1.33      inference('split', [status(esa)], ['0'])).
% 1.15/1.33  thf('76', plain,
% 1.15/1.33      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.15/1.33      inference('sat_resolution*', [status(thm)], ['4', '42', '73', '74', '75'])).
% 1.15/1.33  thf('77', plain,
% 1.15/1.33      (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.15/1.33      inference('simpl_trail', [status(thm)], ['1', '76'])).
% 1.15/1.33  thf('78', plain,
% 1.15/1.33      ((((sk_B_2) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.15/1.33      inference('sup-', [status(thm)], ['9', '16'])).
% 1.15/1.33  thf('79', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 1.15/1.33      inference('sup-', [status(thm)], ['18', '29'])).
% 1.15/1.33  thf('80', plain,
% 1.15/1.33      (![X52 : $i, X53 : $i]:
% 1.15/1.33         (~ (r1_tarski @ (k2_relat_1 @ X52) @ X53)
% 1.15/1.33          | (m1_subset_1 @ X52 @ 
% 1.15/1.33             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X52) @ X53)))
% 1.15/1.33          | ~ (v1_funct_1 @ X52)
% 1.15/1.33          | ~ (v1_relat_1 @ X52))),
% 1.15/1.33      inference('cnf', [status(esa)], [t4_funct_2])).
% 1.15/1.33  thf('81', plain,
% 1.15/1.33      ((~ (v1_relat_1 @ sk_D)
% 1.15/1.33        | ~ (v1_funct_1 @ sk_D)
% 1.15/1.33        | (m1_subset_1 @ sk_D @ 
% 1.15/1.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C))))),
% 1.15/1.33      inference('sup-', [status(thm)], ['79', '80'])).
% 1.15/1.33  thf('82', plain, ((v1_relat_1 @ sk_D)),
% 1.15/1.33      inference('sup-', [status(thm)], ['24', '25'])).
% 1.15/1.33  thf('83', plain, ((v1_funct_1 @ sk_D)),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf('84', plain,
% 1.15/1.33      ((m1_subset_1 @ sk_D @ 
% 1.15/1.33        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 1.15/1.33      inference('demod', [status(thm)], ['81', '82', '83'])).
% 1.15/1.33  thf('85', plain,
% 1.15/1.33      (![X14 : $i, X15 : $i]:
% 1.15/1.33         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.15/1.33      inference('cnf', [status(esa)], [t3_subset])).
% 1.15/1.33  thf('86', plain,
% 1.15/1.33      ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C))),
% 1.15/1.33      inference('sup-', [status(thm)], ['84', '85'])).
% 1.15/1.33  thf('87', plain,
% 1.15/1.33      (((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))
% 1.15/1.33        | ((sk_B_2) = (k1_xboole_0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['78', '86'])).
% 1.15/1.33  thf('88', plain,
% 1.15/1.33      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 1.15/1.33      inference('split', [status(esa)], ['39'])).
% 1.15/1.33  thf('89', plain,
% 1.15/1.33      ((m1_subset_1 @ sk_D @ 
% 1.15/1.33        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 1.15/1.33      inference('demod', [status(thm)], ['81', '82', '83'])).
% 1.15/1.33  thf('90', plain,
% 1.15/1.33      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.15/1.33      inference('sup-', [status(thm)], ['44', '45'])).
% 1.15/1.33  thf('91', plain,
% 1.15/1.33      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.15/1.33      inference('split', [status(esa)], ['39'])).
% 1.15/1.33  thf('92', plain,
% 1.15/1.33      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 1.15/1.33         <= (~
% 1.15/1.33             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 1.15/1.33      inference('split', [status(esa)], ['0'])).
% 1.15/1.33  thf('93', plain,
% 1.15/1.33      ((~ (m1_subset_1 @ sk_D @ 
% 1.15/1.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 1.15/1.33         <= (~
% 1.15/1.33             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 1.15/1.33             (((sk_A) = (k1_xboole_0))))),
% 1.15/1.33      inference('sup-', [status(thm)], ['91', '92'])).
% 1.15/1.33  thf('94', plain,
% 1.15/1.33      ((![X0 : $i]:
% 1.15/1.33          (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))
% 1.15/1.33           | ~ (v1_xboole_0 @ X0)))
% 1.15/1.33         <= (~
% 1.15/1.33             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 1.15/1.33             (((sk_A) = (k1_xboole_0))))),
% 1.15/1.33      inference('sup-', [status(thm)], ['90', '93'])).
% 1.15/1.33  thf('95', plain,
% 1.15/1.33      ((~ (v1_xboole_0 @ (k1_relat_1 @ sk_D)))
% 1.15/1.33         <= (~
% 1.15/1.33             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 1.15/1.33             (((sk_A) = (k1_xboole_0))))),
% 1.15/1.33      inference('sup-', [status(thm)], ['89', '94'])).
% 1.15/1.33  thf('96', plain,
% 1.15/1.33      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.15/1.33      inference('sup-', [status(thm)], ['60', '65'])).
% 1.15/1.33  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.33      inference('sup-', [status(thm)], ['68', '71'])).
% 1.15/1.33  thf('98', plain,
% 1.15/1.33      (~ (((sk_A) = (k1_xboole_0))) | 
% 1.15/1.33       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.15/1.33      inference('demod', [status(thm)], ['95', '96', '97'])).
% 1.15/1.33  thf('99', plain, (~ (((sk_B_2) = (k1_xboole_0)))),
% 1.15/1.33      inference('sat_resolution*', [status(thm)],
% 1.15/1.33                ['4', '42', '73', '75', '98', '74'])).
% 1.15/1.33  thf('100', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.15/1.33      inference('simpl_trail', [status(thm)], ['88', '99'])).
% 1.15/1.33  thf('101', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 1.15/1.33      inference('simplify_reflect-', [status(thm)], ['87', '100'])).
% 1.15/1.33  thf('102', plain,
% 1.15/1.33      (![X14 : $i, X16 : $i]:
% 1.15/1.33         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 1.15/1.33      inference('cnf', [status(esa)], [t3_subset])).
% 1.15/1.33  thf('103', plain,
% 1.15/1.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.15/1.33      inference('sup-', [status(thm)], ['101', '102'])).
% 1.15/1.33  thf('104', plain, ($false), inference('demod', [status(thm)], ['77', '103'])).
% 1.15/1.33  
% 1.15/1.33  % SZS output end Refutation
% 1.15/1.33  
% 1.15/1.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
