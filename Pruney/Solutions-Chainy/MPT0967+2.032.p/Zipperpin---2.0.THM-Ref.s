%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6mzBq97WFc

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:15 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 581 expanded)
%              Number of leaves         :   29 ( 175 expanded)
%              Depth                    :   23
%              Number of atoms          :  977 (7129 expanded)
%              Number of equality atoms :   90 ( 525 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X12 @ X10 ) @ ( k2_zfmisc_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['4','17','18'])).

thf('20',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

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
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('25',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('34',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
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

thf('39',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('42',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('49',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','52'])).

thf('54',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['4','17','18'])).

thf('55',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X28 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('57',plain,(
    ! [X27: $i] :
      ( zip_tseitin_0 @ X27 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('59',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('65',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('68',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('70',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('72',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('77',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29
       != ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
       != ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('82',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','74'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['55','83'])).

thf('85',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('86',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['37','86'])).

thf('88',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['35','87'])).

thf('89',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['30','88'])).

thf('90',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['23','89'])).

thf('91',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29
       != ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('92',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('99',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('100',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['37','86'])).

thf('103',plain,(
    zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_A != sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['92','103'])).

thf('105',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['20','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6mzBq97WFc
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:59:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 274 iterations in 0.174s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.39/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.62  thf(t9_funct_2, conjecture,
% 0.39/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62       ( ( r1_tarski @ B @ C ) =>
% 0.39/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.39/0.62           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.39/0.62             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.62            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62          ( ( r1_tarski @ B @ C ) =>
% 0.39/0.62            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.39/0.62              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.39/0.62                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.39/0.62  thf('0', plain,
% 0.39/0.62      ((~ (v1_funct_1 @ sk_D)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 0.39/0.62        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.39/0.62         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.39/0.62      inference('split', [status(esa)], ['0'])).
% 0.39/0.62  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.39/0.62      inference('split', [status(esa)], ['0'])).
% 0.39/0.62  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.39/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.62  thf('5', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t118_zfmisc_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( r1_tarski @ A @ B ) =>
% 0.39/0.62       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.39/0.62         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.62         (~ (r1_tarski @ X10 @ X11)
% 0.39/0.62          | (r1_tarski @ (k2_zfmisc_1 @ X12 @ X10) @ (k2_zfmisc_1 @ X12 @ X11)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_C_1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.62  thf('8', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t3_subset, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.62  thf('9', plain,
% 0.39/0.62      (![X18 : $i, X19 : $i]:
% 0.39/0.62         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.62  thf('10', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.62  thf(t1_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.39/0.62       ( r1_tarski @ A @ C ) ))).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.62         (~ (r1_tarski @ X3 @ X4)
% 0.39/0.62          | ~ (r1_tarski @ X4 @ X5)
% 0.39/0.62          | (r1_tarski @ X3 @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.39/0.62  thf('12', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((r1_tarski @ sk_D @ X0)
% 0.39/0.62          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.62  thf('13', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['7', '12'])).
% 0.39/0.62  thf('14', plain,
% 0.39/0.62      (![X18 : $i, X20 : $i]:
% 0.39/0.62         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.62  thf('16', plain,
% 0.39/0.62      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.39/0.62         <= (~
% 0.39/0.62             ((m1_subset_1 @ sk_D @ 
% 0.39/0.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.39/0.62      inference('split', [status(esa)], ['0'])).
% 0.39/0.62  thf('17', plain,
% 0.39/0.62      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.62  thf('18', plain,
% 0.39/0.62      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | 
% 0.39/0.62       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 0.39/0.62       ~ ((v1_funct_1 @ sk_D))),
% 0.39/0.62      inference('split', [status(esa)], ['0'])).
% 0.39/0.62  thf('19', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.39/0.62      inference('sat_resolution*', [status(thm)], ['4', '17', '18'])).
% 0.39/0.62  thf('20', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.39/0.62      inference('simpl_trail', [status(thm)], ['1', '19'])).
% 0.39/0.62  thf('21', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.62  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.62  thf('22', plain,
% 0.39/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.39/0.62         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.39/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.62  thf('23', plain,
% 0.39/0.62      (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.39/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.62  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(d1_funct_2, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.39/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.39/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.62  thf(zf_stmt_1, axiom,
% 0.39/0.62    (![C:$i,B:$i,A:$i]:
% 0.39/0.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.39/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.62  thf('25', plain,
% 0.39/0.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.39/0.62         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.39/0.62          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.39/0.62          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.62  thf('26', plain,
% 0.39/0.62      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.39/0.62        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.62  thf('27', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('28', plain,
% 0.39/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.39/0.62         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.39/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.62  thf('29', plain,
% 0.39/0.62      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.39/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.62  thf('30', plain,
% 0.39/0.62      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.39/0.62      inference('demod', [status(thm)], ['26', '29'])).
% 0.39/0.62  thf(zf_stmt_2, axiom,
% 0.39/0.62    (![B:$i,A:$i]:
% 0.39/0.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.62       ( zip_tseitin_0 @ B @ A ) ))).
% 0.39/0.62  thf('31', plain,
% 0.39/0.62      (![X27 : $i, X28 : $i]:
% 0.39/0.62         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.62  thf('32', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.62  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.39/0.62  thf(zf_stmt_5, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.39/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.39/0.62  thf('33', plain,
% 0.39/0.62      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.62         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.39/0.62          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.39/0.62          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.62  thf('34', plain,
% 0.39/0.62      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.62  thf('35', plain,
% 0.39/0.62      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['31', '34'])).
% 0.39/0.62  thf('36', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('37', plain,
% 0.39/0.62      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.39/0.62      inference('split', [status(esa)], ['36'])).
% 0.39/0.62  thf('38', plain,
% 0.39/0.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('split', [status(esa)], ['36'])).
% 0.39/0.62  thf('39', plain,
% 0.39/0.62      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.39/0.62         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.39/0.62      inference('split', [status(esa)], ['0'])).
% 0.39/0.62  thf('40', plain,
% 0.39/0.62      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 0.39/0.62         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.39/0.62             (((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.62  thf(t113_zfmisc_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.62  thf('41', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i]:
% 0.39/0.62         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.62  thf('42', plain,
% 0.39/0.62      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['41'])).
% 0.39/0.62  thf('43', plain,
% 0.39/0.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('split', [status(esa)], ['36'])).
% 0.39/0.62  thf('44', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('45', plain,
% 0.39/0.62      (((m1_subset_1 @ sk_D @ 
% 0.39/0.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup+', [status(thm)], ['43', '44'])).
% 0.39/0.62  thf('46', plain,
% 0.39/0.62      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup+', [status(thm)], ['42', '45'])).
% 0.39/0.62  thf('47', plain,
% 0.39/0.62      (![X18 : $i, X19 : $i]:
% 0.39/0.62         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.62  thf('48', plain,
% 0.39/0.62      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.39/0.62  thf('49', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.39/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.62  thf(d10_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.62  thf('50', plain,
% 0.39/0.62      (![X0 : $i, X2 : $i]:
% 0.39/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.62  thf('51', plain,
% 0.39/0.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.39/0.62  thf('52', plain,
% 0.39/0.62      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['48', '51'])).
% 0.39/0.62  thf('53', plain,
% 0.39/0.62      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))
% 0.39/0.62         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.39/0.62             (((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('demod', [status(thm)], ['40', '52'])).
% 0.39/0.62  thf('54', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.39/0.62      inference('sat_resolution*', [status(thm)], ['4', '17', '18'])).
% 0.39/0.62  thf('55', plain,
% 0.39/0.62      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('simpl_trail', [status(thm)], ['53', '54'])).
% 0.39/0.62  thf('56', plain,
% 0.39/0.62      (![X27 : $i, X28 : $i]:
% 0.39/0.62         ((zip_tseitin_0 @ X27 @ X28) | ((X28) != (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.62  thf('57', plain, (![X27 : $i]: (zip_tseitin_0 @ X27 @ k1_xboole_0)),
% 0.39/0.62      inference('simplify', [status(thm)], ['56'])).
% 0.39/0.62  thf('58', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.39/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.62  thf('59', plain,
% 0.39/0.62      (![X18 : $i, X20 : $i]:
% 0.39/0.62         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.62  thf('60', plain,
% 0.39/0.62      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['58', '59'])).
% 0.39/0.62  thf('61', plain,
% 0.39/0.62      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.62         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.39/0.62          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.39/0.62          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.62  thf('62', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.39/0.62  thf('63', plain,
% 0.39/0.62      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.39/0.62      inference('sup-', [status(thm)], ['57', '62'])).
% 0.39/0.62  thf('64', plain,
% 0.39/0.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('split', [status(esa)], ['36'])).
% 0.39/0.62  thf('65', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('66', plain,
% 0.39/0.62      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup+', [status(thm)], ['64', '65'])).
% 0.39/0.62  thf('67', plain,
% 0.39/0.62      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['48', '51'])).
% 0.39/0.62  thf('68', plain,
% 0.39/0.62      (((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('demod', [status(thm)], ['66', '67'])).
% 0.39/0.62  thf('69', plain,
% 0.39/0.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.39/0.62         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.39/0.62          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.39/0.62          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.62  thf('70', plain,
% 0.39/0.62      (((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0)
% 0.39/0.62         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0))))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.39/0.62  thf('71', plain,
% 0.39/0.62      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['58', '59'])).
% 0.39/0.62  thf('72', plain,
% 0.39/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.39/0.62         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.39/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.62  thf('73', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['71', '72'])).
% 0.39/0.62  thf('74', plain,
% 0.39/0.62      (((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0)
% 0.39/0.62         | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('demod', [status(thm)], ['70', '73'])).
% 0.39/0.62  thf('75', plain,
% 0.39/0.62      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['63', '74'])).
% 0.39/0.62  thf('76', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['71', '72'])).
% 0.39/0.62  thf('77', plain,
% 0.39/0.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.39/0.62         (((X29) != (k1_relset_1 @ X29 @ X30 @ X31))
% 0.39/0.62          | (v1_funct_2 @ X31 @ X29 @ X30)
% 0.39/0.62          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.62  thf('78', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((X1) != (k1_relat_1 @ k1_xboole_0))
% 0.39/0.62          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.39/0.62          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['76', '77'])).
% 0.39/0.62  thf('79', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 0.39/0.62          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ (k1_relat_1 @ k1_xboole_0)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['78'])).
% 0.39/0.62  thf('80', plain,
% 0.39/0.62      ((![X0 : $i]:
% 0.39/0.62          (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 0.39/0.62           | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['75', '79'])).
% 0.39/0.62  thf('81', plain,
% 0.39/0.62      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.39/0.62      inference('sup-', [status(thm)], ['57', '62'])).
% 0.39/0.62  thf('82', plain,
% 0.39/0.62      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['63', '74'])).
% 0.39/0.62  thf('83', plain,
% 0.39/0.62      ((![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.39/0.62  thf('84', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['55', '83'])).
% 0.39/0.62  thf('85', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('split', [status(esa)], ['36'])).
% 0.39/0.62  thf('86', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('sat_resolution*', [status(thm)], ['84', '85'])).
% 0.39/0.62  thf('87', plain, (((sk_B) != (k1_xboole_0))),
% 0.39/0.62      inference('simpl_trail', [status(thm)], ['37', '86'])).
% 0.39/0.62  thf('88', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['35', '87'])).
% 0.39/0.62  thf('89', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.39/0.62      inference('demod', [status(thm)], ['30', '88'])).
% 0.39/0.62  thf('90', plain, (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['23', '89'])).
% 0.39/0.62  thf('91', plain,
% 0.39/0.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.39/0.62         (((X29) != (k1_relset_1 @ X29 @ X30 @ X31))
% 0.39/0.62          | (v1_funct_2 @ X31 @ X29 @ X30)
% 0.39/0.62          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.62  thf('92', plain,
% 0.39/0.62      ((((sk_A) != (sk_A))
% 0.39/0.62        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 0.39/0.62        | (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['90', '91'])).
% 0.39/0.62  thf('93', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('94', plain,
% 0.39/0.62      (![X27 : $i, X28 : $i]:
% 0.39/0.62         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.62  thf('95', plain,
% 0.39/0.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.39/0.62  thf('96', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         (~ (r1_tarski @ X1 @ X0)
% 0.39/0.62          | (zip_tseitin_0 @ X0 @ X2)
% 0.39/0.62          | ((X1) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['94', '95'])).
% 0.39/0.62  thf('97', plain,
% 0.39/0.62      (![X0 : $i]: (((sk_B) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_C_1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['93', '96'])).
% 0.39/0.62  thf('98', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.62  thf('99', plain,
% 0.39/0.62      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.62         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.39/0.62          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.39/0.62          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.62  thf('100', plain,
% 0.39/0.62      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 0.39/0.62        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['98', '99'])).
% 0.39/0.62  thf('101', plain,
% 0.39/0.62      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['97', '100'])).
% 0.39/0.62  thf('102', plain, (((sk_B) != (k1_xboole_0))),
% 0.39/0.62      inference('simpl_trail', [status(thm)], ['37', '86'])).
% 0.39/0.62  thf('103', plain, ((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 0.39/0.62  thf('104', plain,
% 0.39/0.62      ((((sk_A) != (sk_A)) | (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.39/0.62      inference('demod', [status(thm)], ['92', '103'])).
% 0.39/0.62  thf('105', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.39/0.62      inference('simplify', [status(thm)], ['104'])).
% 0.39/0.62  thf('106', plain, ($false), inference('demod', [status(thm)], ['20', '105'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.45/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
