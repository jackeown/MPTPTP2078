%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bAvTvuSldw

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:44 EST 2020

% Result     : Theorem 29.84s
% Output     : Refutation 29.84s
% Verified   : 
% Statistics : Number of formulae       :  316 (4875 expanded)
%              Number of leaves         :   44 (1466 expanded)
%              Depth                    :   35
%              Number of atoms          : 2649 (50249 expanded)
%              Number of equality atoms :  189 (3650 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('1',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ( ( k2_partfun1 @ X52 @ X53 @ X51 @ X54 )
        = ( k7_relat_1 @ X51 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['1','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X48 @ X49 @ X47 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('16',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('21',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['19','21'])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( r1_tarski @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('41',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X21 @ X22 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('42',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('47',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','47'])).

thf('49',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X21 @ X22 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('50',plain,
    ( ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','46'])).

thf('52',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('56',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('59',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','46'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('64',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('65',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( r1_tarski @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['40','66'])).

thf('68',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('71',plain,(
    ! [X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( v4_relat_1 @ sk_D @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('72',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('75',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('78',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('81',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('82',plain,
    ( ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('86',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('87',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_A )
        | ~ ( v1_relat_1 @ sk_D )
        | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
          = X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['76','77'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_A )
        | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
          = X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
      = sk_C )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('94',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['92','93'])).

thf(fc23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v4_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('95',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X15 )
      | ~ ( v4_relat_1 @ X14 @ X16 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['76','77'])).

thf('98',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['92','93'])).

thf('102',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
      | ~ ( v4_relat_1 @ X14 @ X16 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['76','77'])).

thf('105',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['100','105'])).

thf('107',plain,
    ( ( r1_tarski @ sk_C @ sk_C )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['91','106'])).

thf('108',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
      = sk_C )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','90'])).

thf('109',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['92','93'])).

thf('110',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('111',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['76','77'])).

thf('113',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X21 @ X22 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('115',plain,
    ( ( r1_tarski @ sk_D @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['76','77'])).

thf('117',plain,(
    r1_tarski @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X21 @ X22 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['76','77'])).

thf('123',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_D ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ( ( r1_tarski @ A @ D )
       => ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('125',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r1_tarski @ X35 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_relset_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['123','126'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('128',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X31 ) @ X32 )
      | ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C @ X0 )
        | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['108','129'])).

thf('131',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['107','130'])).

thf('132',plain,(
    m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','131'])).

thf('133',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('134',plain,(
    ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['14','132','133'])).

thf('135',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['7','134'])).

thf('136',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('138',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_B = X1 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['142'])).

thf('144',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['141','143'])).

thf('145',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('147',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('149',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('150',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['147','152'])).

thf('154',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 != k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ( X46 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('155',plain,(
    ! [X45: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X45 @ k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('157',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('158',plain,(
    ! [X45: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X45 @ k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('162',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['160','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['153','167'])).

thf('169',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['153','167'])).

thf('170',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X1 = X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( X1 = X0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['171'])).

thf('173',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('174',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_A )
        | ~ ( v1_relat_1 @ sk_D )
        | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
          = X0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['76','77'])).

thf('176',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_A )
        | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
          = X0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
      = sk_C )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','176'])).

thf('178',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['142'])).

thf('179',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('182',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('184',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('186',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('190',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ( ( k2_partfun1 @ X52 @ X53 @ X51 @ X54 )
        = ( k7_relat_1 @ X51 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('191',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','47'])).

thf('193',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['188','193'])).

thf('195',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('196',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['142'])).

thf('197',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('198',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['142'])).

thf('200',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('203',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('205',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['198','203','204'])).

thf('206',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['195','205'])).

thf('207',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['194','206'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('209',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41
       != ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X40 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('213',plain,(
    ! [X39: $i] :
      ( zip_tseitin_0 @ X39 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('215',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['211','215'])).

thf('217',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['207','216'])).

thf('218',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['142'])).

thf('219',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['14','132','133','217','218'])).

thf('220',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference(simpl_trail,[status(thm)],['177','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['100','105'])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('223',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ sk_B @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41
       != ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('229',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ~ ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('232',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('233',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('234',plain,(
    ! [X45: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X45 @ k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('235',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X0 @ X1 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X4 )
      | ( X1 = k1_xboole_0 )
      | ( zip_tseitin_0 @ X2 @ X3 ) ) ),
    inference('sup+',[status(thm)],['232','235'])).

thf('237',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( X2 = k1_xboole_0 )
      | ( v1_funct_2 @ X1 @ X2 @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['211','215'])).

thf('239',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ X2 @ X0 @ X2 )
      | ( zip_tseitin_0 @ X2 @ X3 ) ) ),
    inference('sup+',[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['239'])).

thf('241',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('242',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('244',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['211','215'])).

thf('246',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X2 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['244','245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['246'])).

thf('248',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['231','247'])).

thf('249',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['19','21'])).

thf('250',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('253',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['76','77'])).

thf('255',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['253','254'])).

thf('256',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('257',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( ( k7_relat_1 @ sk_D @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('259',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('260',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_C @ sk_B )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['257','260'])).

thf('262',plain,(
    ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['14','132','133'])).

thf('263',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_C @ sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['261','262'])).

thf('264',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['248','263'])).

thf('265',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(condensation,[status(thm)],['264'])).

thf('266',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 ) ),
    inference(demod,[status(thm)],['230','265'])).

thf('267',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['227','266'])).

thf('268',plain,
    ( ( sk_C != sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['220','267'])).

thf('269',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference(simplify,[status(thm)],['268'])).

thf('270',plain,(
    $false ),
    inference(demod,[status(thm)],['135','269'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bAvTvuSldw
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 29.84/30.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 29.84/30.08  % Solved by: fo/fo7.sh
% 29.84/30.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 29.84/30.08  % done 21739 iterations in 29.587s
% 29.84/30.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 29.84/30.08  % SZS output start Refutation
% 29.84/30.08  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 29.84/30.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 29.84/30.08  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 29.84/30.08  thf(sk_D_type, type, sk_D: $i).
% 29.84/30.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 29.84/30.08  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 29.84/30.08  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 29.84/30.08  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 29.84/30.08  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 29.84/30.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 29.84/30.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 29.84/30.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 29.84/30.08  thf(sk_B_type, type, sk_B: $i).
% 29.84/30.08  thf(sk_C_type, type, sk_C: $i).
% 29.84/30.08  thf(sk_A_type, type, sk_A: $i).
% 29.84/30.08  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 29.84/30.08  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 29.84/30.08  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 29.84/30.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 29.84/30.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 29.84/30.08  thf(t38_funct_2, conjecture,
% 29.84/30.08    (![A:$i,B:$i,C:$i,D:$i]:
% 29.84/30.08     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 29.84/30.08         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 29.84/30.08       ( ( r1_tarski @ C @ A ) =>
% 29.84/30.08         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 29.84/30.08           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 29.84/30.08             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 29.84/30.08             ( m1_subset_1 @
% 29.84/30.08               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 29.84/30.08               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 29.84/30.08  thf(zf_stmt_0, negated_conjecture,
% 29.84/30.08    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 29.84/30.08        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 29.84/30.08            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 29.84/30.08          ( ( r1_tarski @ C @ A ) =>
% 29.84/30.08            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 29.84/30.08              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 29.84/30.08                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 29.84/30.08                ( m1_subset_1 @
% 29.84/30.08                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 29.84/30.08                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 29.84/30.08    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 29.84/30.08  thf('0', plain,
% 29.84/30.08      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 29.84/30.08        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 29.84/30.08             sk_B)
% 29.84/30.08        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.08             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 29.84/30.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.08  thf('1', plain,
% 29.84/30.08      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))
% 29.84/30.08         <= (~
% 29.84/30.08             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 29.84/30.08               sk_B)))),
% 29.84/30.08      inference('split', [status(esa)], ['0'])).
% 29.84/30.08  thf('2', plain,
% 29.84/30.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 29.84/30.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.08  thf(redefinition_k2_partfun1, axiom,
% 29.84/30.08    (![A:$i,B:$i,C:$i,D:$i]:
% 29.84/30.08     ( ( ( v1_funct_1 @ C ) & 
% 29.84/30.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 29.84/30.08       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 29.84/30.08  thf('3', plain,
% 29.84/30.08      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 29.84/30.08         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 29.84/30.08          | ~ (v1_funct_1 @ X51)
% 29.84/30.08          | ((k2_partfun1 @ X52 @ X53 @ X51 @ X54) = (k7_relat_1 @ X51 @ X54)))),
% 29.84/30.08      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 29.84/30.08  thf('4', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 29.84/30.08          | ~ (v1_funct_1 @ sk_D))),
% 29.84/30.08      inference('sup-', [status(thm)], ['2', '3'])).
% 29.84/30.08  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 29.84/30.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.08  thf('6', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 29.84/30.08      inference('demod', [status(thm)], ['4', '5'])).
% 29.84/30.08  thf('7', plain,
% 29.84/30.08      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))
% 29.84/30.08         <= (~
% 29.84/30.08             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 29.84/30.08               sk_B)))),
% 29.84/30.08      inference('demod', [status(thm)], ['1', '6'])).
% 29.84/30.08  thf('8', plain,
% 29.84/30.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 29.84/30.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.08  thf(dt_k2_partfun1, axiom,
% 29.84/30.08    (![A:$i,B:$i,C:$i,D:$i]:
% 29.84/30.08     ( ( ( v1_funct_1 @ C ) & 
% 29.84/30.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 29.84/30.08       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 29.84/30.08         ( m1_subset_1 @
% 29.84/30.08           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 29.84/30.08           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 29.84/30.08  thf('9', plain,
% 29.84/30.08      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 29.84/30.08         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 29.84/30.08          | ~ (v1_funct_1 @ X47)
% 29.84/30.08          | (v1_funct_1 @ (k2_partfun1 @ X48 @ X49 @ X47 @ X50)))),
% 29.84/30.08      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 29.84/30.08  thf('10', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 29.84/30.08          | ~ (v1_funct_1 @ sk_D))),
% 29.84/30.08      inference('sup-', [status(thm)], ['8', '9'])).
% 29.84/30.08  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 29.84/30.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.08  thf('12', plain,
% 29.84/30.08      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 29.84/30.08      inference('demod', [status(thm)], ['10', '11'])).
% 29.84/30.08  thf('13', plain,
% 29.84/30.08      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))
% 29.84/30.08         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))))),
% 29.84/30.08      inference('split', [status(esa)], ['0'])).
% 29.84/30.08  thf('14', plain,
% 29.84/30.08      (((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 29.84/30.08      inference('sup-', [status(thm)], ['12', '13'])).
% 29.84/30.08  thf('15', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 29.84/30.08      inference('demod', [status(thm)], ['4', '5'])).
% 29.84/30.08  thf('16', plain,
% 29.84/30.08      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 29.84/30.08         <= (~
% 29.84/30.08             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 29.84/30.08      inference('split', [status(esa)], ['0'])).
% 29.84/30.08  thf('17', plain,
% 29.84/30.08      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 29.84/30.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 29.84/30.08         <= (~
% 29.84/30.08             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 29.84/30.08      inference('sup-', [status(thm)], ['15', '16'])).
% 29.84/30.08  thf('18', plain, ((r1_tarski @ sk_C @ sk_A)),
% 29.84/30.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.08  thf(d1_funct_2, axiom,
% 29.84/30.08    (![A:$i,B:$i,C:$i]:
% 29.84/30.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.84/30.08       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 29.84/30.08           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 29.84/30.08             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 29.84/30.08         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 29.84/30.08           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 29.84/30.08             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 29.84/30.08  thf(zf_stmt_1, axiom,
% 29.84/30.08    (![B:$i,A:$i]:
% 29.84/30.08     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 29.84/30.08       ( zip_tseitin_0 @ B @ A ) ))).
% 29.84/30.08  thf('19', plain,
% 29.84/30.08      (![X39 : $i, X40 : $i]:
% 29.84/30.08         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 29.84/30.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 29.84/30.08  thf(t113_zfmisc_1, axiom,
% 29.84/30.08    (![A:$i,B:$i]:
% 29.84/30.08     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 29.84/30.08       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 29.84/30.08  thf('20', plain,
% 29.84/30.08      (![X5 : $i, X6 : $i]:
% 29.84/30.08         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 29.84/30.08      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 29.84/30.08  thf('21', plain,
% 29.84/30.08      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 29.84/30.08      inference('simplify', [status(thm)], ['20'])).
% 29.84/30.08  thf('22', plain,
% 29.84/30.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.84/30.08         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 29.84/30.08      inference('sup+', [status(thm)], ['19', '21'])).
% 29.84/30.08  thf('23', plain,
% 29.84/30.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 29.84/30.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.08  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 29.84/30.08  thf(zf_stmt_3, axiom,
% 29.84/30.08    (![C:$i,B:$i,A:$i]:
% 29.84/30.08     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 29.84/30.08       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 29.84/30.08  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 29.84/30.08  thf(zf_stmt_5, axiom,
% 29.84/30.08    (![A:$i,B:$i,C:$i]:
% 29.84/30.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.84/30.08       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 29.84/30.08         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 29.84/30.08           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 29.84/30.08             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 29.84/30.08  thf('24', plain,
% 29.84/30.08      (![X44 : $i, X45 : $i, X46 : $i]:
% 29.84/30.08         (~ (zip_tseitin_0 @ X44 @ X45)
% 29.84/30.08          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 29.84/30.08          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 29.84/30.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 29.84/30.08  thf('25', plain,
% 29.84/30.08      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 29.84/30.08      inference('sup-', [status(thm)], ['23', '24'])).
% 29.84/30.08  thf('26', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 29.84/30.08          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 29.84/30.08      inference('sup-', [status(thm)], ['22', '25'])).
% 29.84/30.08  thf('27', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 29.84/30.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.08  thf('28', plain,
% 29.84/30.08      (![X41 : $i, X42 : $i, X43 : $i]:
% 29.84/30.08         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 29.84/30.08          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 29.84/30.08          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 29.84/30.08      inference('cnf', [status(esa)], [zf_stmt_3])).
% 29.84/30.08  thf('29', plain,
% 29.84/30.08      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 29.84/30.08        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 29.84/30.08      inference('sup-', [status(thm)], ['27', '28'])).
% 29.84/30.08  thf('30', plain,
% 29.84/30.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 29.84/30.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.08  thf(redefinition_k1_relset_1, axiom,
% 29.84/30.08    (![A:$i,B:$i,C:$i]:
% 29.84/30.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.84/30.08       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 29.84/30.08  thf('31', plain,
% 29.84/30.08      (![X28 : $i, X29 : $i, X30 : $i]:
% 29.84/30.08         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 29.84/30.08          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 29.84/30.08      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 29.84/30.08  thf('32', plain,
% 29.84/30.08      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 29.84/30.08      inference('sup-', [status(thm)], ['30', '31'])).
% 29.84/30.08  thf('33', plain,
% 29.84/30.08      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 29.84/30.08      inference('demod', [status(thm)], ['29', '32'])).
% 29.84/30.08  thf('34', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 29.84/30.08          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 29.84/30.08      inference('sup-', [status(thm)], ['26', '33'])).
% 29.84/30.08  thf('35', plain,
% 29.84/30.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 29.84/30.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.08  thf(t3_subset, axiom,
% 29.84/30.08    (![A:$i,B:$i]:
% 29.84/30.08     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 29.84/30.08  thf('36', plain,
% 29.84/30.08      (![X7 : $i, X8 : $i]:
% 29.84/30.08         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 29.84/30.08      inference('cnf', [status(esa)], [t3_subset])).
% 29.84/30.08  thf('37', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 29.84/30.08      inference('sup-', [status(thm)], ['35', '36'])).
% 29.84/30.08  thf(t1_xboole_1, axiom,
% 29.84/30.08    (![A:$i,B:$i,C:$i]:
% 29.84/30.08     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 29.84/30.08       ( r1_tarski @ A @ C ) ))).
% 29.84/30.08  thf('38', plain,
% 29.84/30.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.84/30.08         (~ (r1_tarski @ X0 @ X1)
% 29.84/30.08          | ~ (r1_tarski @ X1 @ X2)
% 29.84/30.08          | (r1_tarski @ X0 @ X2))),
% 29.84/30.08      inference('cnf', [status(esa)], [t1_xboole_1])).
% 29.84/30.08  thf('39', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         ((r1_tarski @ sk_D @ X0)
% 29.84/30.08          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0))),
% 29.84/30.08      inference('sup-', [status(thm)], ['37', '38'])).
% 29.84/30.08  thf('40', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 29.84/30.08          | ((sk_A) = (k1_relat_1 @ sk_D))
% 29.84/30.08          | (r1_tarski @ sk_D @ X0))),
% 29.84/30.08      inference('sup-', [status(thm)], ['34', '39'])).
% 29.84/30.08  thf(t88_relat_1, axiom,
% 29.84/30.08    (![A:$i,B:$i]:
% 29.84/30.08     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 29.84/30.08  thf('41', plain,
% 29.84/30.08      (![X21 : $i, X22 : $i]:
% 29.84/30.08         ((r1_tarski @ (k7_relat_1 @ X21 @ X22) @ X21) | ~ (v1_relat_1 @ X21))),
% 29.84/30.08      inference('cnf', [status(esa)], [t88_relat_1])).
% 29.84/30.08  thf(t3_xboole_1, axiom,
% 29.84/30.08    (![A:$i]:
% 29.84/30.08     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 29.84/30.08  thf('42', plain,
% 29.84/30.08      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 29.84/30.08      inference('cnf', [status(esa)], [t3_xboole_1])).
% 29.84/30.08  thf('43', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         (~ (v1_relat_1 @ k1_xboole_0)
% 29.84/30.08          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 29.84/30.08      inference('sup-', [status(thm)], ['41', '42'])).
% 29.84/30.08  thf('44', plain,
% 29.84/30.08      (![X5 : $i, X6 : $i]:
% 29.84/30.08         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 29.84/30.08      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 29.84/30.08  thf('45', plain,
% 29.84/30.08      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 29.84/30.08      inference('simplify', [status(thm)], ['44'])).
% 29.84/30.08  thf(fc6_relat_1, axiom,
% 29.84/30.08    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 29.84/30.08  thf('46', plain,
% 29.84/30.08      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 29.84/30.08      inference('cnf', [status(esa)], [fc6_relat_1])).
% 29.84/30.08  thf('47', plain, ((v1_relat_1 @ k1_xboole_0)),
% 29.84/30.08      inference('sup+', [status(thm)], ['45', '46'])).
% 29.84/30.08  thf('48', plain,
% 29.84/30.08      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 29.84/30.08      inference('demod', [status(thm)], ['43', '47'])).
% 29.84/30.08  thf('49', plain,
% 29.84/30.08      (![X21 : $i, X22 : $i]:
% 29.84/30.08         ((r1_tarski @ (k7_relat_1 @ X21 @ X22) @ X21) | ~ (v1_relat_1 @ X21))),
% 29.84/30.08      inference('cnf', [status(esa)], [t88_relat_1])).
% 29.84/30.08  thf('50', plain,
% 29.84/30.08      (((r1_tarski @ k1_xboole_0 @ k1_xboole_0) | ~ (v1_relat_1 @ k1_xboole_0))),
% 29.84/30.08      inference('sup+', [status(thm)], ['48', '49'])).
% 29.84/30.08  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 29.84/30.08      inference('sup+', [status(thm)], ['45', '46'])).
% 29.84/30.08  thf('52', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 29.84/30.08      inference('demod', [status(thm)], ['50', '51'])).
% 29.84/30.08  thf('53', plain,
% 29.84/30.08      (![X7 : $i, X9 : $i]:
% 29.84/30.08         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 29.84/30.08      inference('cnf', [status(esa)], [t3_subset])).
% 29.84/30.08  thf('54', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 29.84/30.08      inference('sup-', [status(thm)], ['52', '53'])).
% 29.84/30.08  thf('55', plain,
% 29.84/30.08      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 29.84/30.08      inference('simplify', [status(thm)], ['20'])).
% 29.84/30.08  thf(cc2_relset_1, axiom,
% 29.84/30.08    (![A:$i,B:$i,C:$i]:
% 29.84/30.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.84/30.08       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 29.84/30.08  thf('56', plain,
% 29.84/30.08      (![X25 : $i, X26 : $i, X27 : $i]:
% 29.84/30.08         ((v4_relat_1 @ X25 @ X26)
% 29.84/30.08          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 29.84/30.08      inference('cnf', [status(esa)], [cc2_relset_1])).
% 29.84/30.08  thf('57', plain,
% 29.84/30.08      (![X0 : $i, X1 : $i]:
% 29.84/30.08         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 29.84/30.08          | (v4_relat_1 @ X1 @ X0))),
% 29.84/30.08      inference('sup-', [status(thm)], ['55', '56'])).
% 29.84/30.08  thf('58', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 29.84/30.08      inference('sup-', [status(thm)], ['54', '57'])).
% 29.84/30.08  thf(d18_relat_1, axiom,
% 29.84/30.08    (![A:$i,B:$i]:
% 29.84/30.08     ( ( v1_relat_1 @ B ) =>
% 29.84/30.08       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 29.84/30.08  thf('59', plain,
% 29.84/30.08      (![X12 : $i, X13 : $i]:
% 29.84/30.08         (~ (v4_relat_1 @ X12 @ X13)
% 29.84/30.08          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 29.84/30.08          | ~ (v1_relat_1 @ X12))),
% 29.84/30.08      inference('cnf', [status(esa)], [d18_relat_1])).
% 29.84/30.08  thf('60', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         (~ (v1_relat_1 @ k1_xboole_0)
% 29.84/30.08          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 29.84/30.08      inference('sup-', [status(thm)], ['58', '59'])).
% 29.84/30.08  thf('61', plain, ((v1_relat_1 @ k1_xboole_0)),
% 29.84/30.08      inference('sup+', [status(thm)], ['45', '46'])).
% 29.84/30.08  thf('62', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 29.84/30.08      inference('demod', [status(thm)], ['60', '61'])).
% 29.84/30.08  thf('63', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 29.84/30.08      inference('demod', [status(thm)], ['60', '61'])).
% 29.84/30.08  thf('64', plain,
% 29.84/30.08      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 29.84/30.08      inference('cnf', [status(esa)], [t3_xboole_1])).
% 29.84/30.08  thf('65', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 29.84/30.08      inference('sup-', [status(thm)], ['63', '64'])).
% 29.84/30.08  thf('66', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 29.84/30.08      inference('demod', [status(thm)], ['62', '65'])).
% 29.84/30.08  thf('67', plain,
% 29.84/30.08      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | (r1_tarski @ sk_D @ X0))),
% 29.84/30.08      inference('demod', [status(thm)], ['40', '66'])).
% 29.84/30.08  thf('68', plain,
% 29.84/30.08      (![X7 : $i, X9 : $i]:
% 29.84/30.08         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 29.84/30.08      inference('cnf', [status(esa)], [t3_subset])).
% 29.84/30.08  thf('69', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         (((sk_A) = (k1_relat_1 @ sk_D))
% 29.84/30.08          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0)))),
% 29.84/30.08      inference('sup-', [status(thm)], ['67', '68'])).
% 29.84/30.08  thf('70', plain,
% 29.84/30.08      (![X25 : $i, X26 : $i, X27 : $i]:
% 29.84/30.08         ((v4_relat_1 @ X25 @ X26)
% 29.84/30.08          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 29.84/30.08      inference('cnf', [status(esa)], [cc2_relset_1])).
% 29.84/30.08  thf('71', plain,
% 29.84/30.08      (![X1 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | (v4_relat_1 @ sk_D @ X1))),
% 29.84/30.08      inference('sup-', [status(thm)], ['69', '70'])).
% 29.84/30.08  thf(t209_relat_1, axiom,
% 29.84/30.08    (![A:$i,B:$i]:
% 29.84/30.08     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 29.84/30.08       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 29.84/30.08  thf('72', plain,
% 29.84/30.08      (![X19 : $i, X20 : $i]:
% 29.84/30.08         (((X19) = (k7_relat_1 @ X19 @ X20))
% 29.84/30.08          | ~ (v4_relat_1 @ X19 @ X20)
% 29.84/30.08          | ~ (v1_relat_1 @ X19))),
% 29.84/30.08      inference('cnf', [status(esa)], [t209_relat_1])).
% 29.84/30.08  thf('73', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         (((sk_A) = (k1_relat_1 @ sk_D))
% 29.84/30.08          | ~ (v1_relat_1 @ sk_D)
% 29.84/30.08          | ((sk_D) = (k7_relat_1 @ sk_D @ X0)))),
% 29.84/30.08      inference('sup-', [status(thm)], ['71', '72'])).
% 29.84/30.08  thf('74', plain,
% 29.84/30.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 29.84/30.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.08  thf(cc2_relat_1, axiom,
% 29.84/30.08    (![A:$i]:
% 29.84/30.08     ( ( v1_relat_1 @ A ) =>
% 29.84/30.08       ( ![B:$i]:
% 29.84/30.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 29.84/30.08  thf('75', plain,
% 29.84/30.08      (![X10 : $i, X11 : $i]:
% 29.84/30.08         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 29.84/30.08          | (v1_relat_1 @ X10)
% 29.84/30.08          | ~ (v1_relat_1 @ X11))),
% 29.84/30.08      inference('cnf', [status(esa)], [cc2_relat_1])).
% 29.84/30.08  thf('76', plain,
% 29.84/30.08      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 29.84/30.08      inference('sup-', [status(thm)], ['74', '75'])).
% 29.84/30.08  thf('77', plain,
% 29.84/30.08      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 29.84/30.08      inference('cnf', [status(esa)], [fc6_relat_1])).
% 29.84/30.08  thf('78', plain, ((v1_relat_1 @ sk_D)),
% 29.84/30.08      inference('demod', [status(thm)], ['76', '77'])).
% 29.84/30.08  thf('79', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         (((sk_A) = (k1_relat_1 @ sk_D)) | ((sk_D) = (k7_relat_1 @ sk_D @ X0)))),
% 29.84/30.08      inference('demod', [status(thm)], ['73', '78'])).
% 29.84/30.08  thf('80', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 29.84/30.08          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 29.84/30.08      inference('sup-', [status(thm)], ['26', '33'])).
% 29.84/30.08  thf('81', plain,
% 29.84/30.08      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 29.84/30.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 29.84/30.08         <= (~
% 29.84/30.08             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 29.84/30.08      inference('sup-', [status(thm)], ['15', '16'])).
% 29.84/30.08  thf('82', plain,
% 29.84/30.08      (((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 29.84/30.08            (k1_zfmisc_1 @ k1_xboole_0))
% 29.84/30.08         | ((sk_A) = (k1_relat_1 @ sk_D))))
% 29.84/30.08         <= (~
% 29.84/30.08             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 29.84/30.08      inference('sup-', [status(thm)], ['80', '81'])).
% 29.84/30.08  thf('83', plain,
% 29.84/30.08      (((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))
% 29.84/30.08         | ((sk_A) = (k1_relat_1 @ sk_D))
% 29.84/30.08         | ((sk_A) = (k1_relat_1 @ sk_D))))
% 29.84/30.08         <= (~
% 29.84/30.08             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 29.84/30.08      inference('sup-', [status(thm)], ['79', '82'])).
% 29.84/30.08  thf('84', plain,
% 29.84/30.08      (((((sk_A) = (k1_relat_1 @ sk_D))
% 29.84/30.08         | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))))
% 29.84/30.08         <= (~
% 29.84/30.08             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 29.84/30.08      inference('simplify', [status(thm)], ['83'])).
% 29.84/30.08  thf('85', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         (((sk_A) = (k1_relat_1 @ sk_D))
% 29.84/30.08          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0)))),
% 29.84/30.08      inference('sup-', [status(thm)], ['67', '68'])).
% 29.84/30.08  thf('86', plain,
% 29.84/30.08      ((((sk_A) = (k1_relat_1 @ sk_D)))
% 29.84/30.08         <= (~
% 29.84/30.08             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 29.84/30.08      inference('clc', [status(thm)], ['84', '85'])).
% 29.84/30.08  thf(t91_relat_1, axiom,
% 29.84/30.08    (![A:$i,B:$i]:
% 29.84/30.08     ( ( v1_relat_1 @ B ) =>
% 29.84/30.08       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 29.84/30.08         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 29.84/30.08  thf('87', plain,
% 29.84/30.08      (![X23 : $i, X24 : $i]:
% 29.84/30.08         (~ (r1_tarski @ X23 @ (k1_relat_1 @ X24))
% 29.84/30.08          | ((k1_relat_1 @ (k7_relat_1 @ X24 @ X23)) = (X23))
% 29.84/30.08          | ~ (v1_relat_1 @ X24))),
% 29.84/30.08      inference('cnf', [status(esa)], [t91_relat_1])).
% 29.84/30.08  thf('88', plain,
% 29.84/30.08      ((![X0 : $i]:
% 29.84/30.08          (~ (r1_tarski @ X0 @ sk_A)
% 29.84/30.08           | ~ (v1_relat_1 @ sk_D)
% 29.84/30.08           | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0))))
% 29.84/30.08         <= (~
% 29.84/30.08             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 29.84/30.08      inference('sup-', [status(thm)], ['86', '87'])).
% 29.84/30.08  thf('89', plain, ((v1_relat_1 @ sk_D)),
% 29.84/30.08      inference('demod', [status(thm)], ['76', '77'])).
% 29.84/30.08  thf('90', plain,
% 29.84/30.08      ((![X0 : $i]:
% 29.84/30.08          (~ (r1_tarski @ X0 @ sk_A)
% 29.84/30.08           | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0))))
% 29.84/30.08         <= (~
% 29.84/30.08             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 29.84/30.08      inference('demod', [status(thm)], ['88', '89'])).
% 29.84/30.08  thf('91', plain,
% 29.84/30.08      ((((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C)))
% 29.84/30.08         <= (~
% 29.84/30.08             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 29.84/30.08      inference('sup-', [status(thm)], ['18', '90'])).
% 29.84/30.08  thf('92', plain,
% 29.84/30.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 29.84/30.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.08  thf('93', plain,
% 29.84/30.08      (![X25 : $i, X26 : $i, X27 : $i]:
% 29.84/30.08         ((v4_relat_1 @ X25 @ X26)
% 29.84/30.08          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 29.84/30.08      inference('cnf', [status(esa)], [cc2_relset_1])).
% 29.84/30.08  thf('94', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 29.84/30.08      inference('sup-', [status(thm)], ['92', '93'])).
% 29.84/30.08  thf(fc23_relat_1, axiom,
% 29.84/30.08    (![A:$i,B:$i,C:$i]:
% 29.84/30.08     ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ B ) ) =>
% 29.84/30.08       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 29.84/30.08         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A ) & 
% 29.84/30.08         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 29.84/30.08  thf('95', plain,
% 29.84/30.08      (![X14 : $i, X15 : $i, X16 : $i]:
% 29.84/30.08         ((v4_relat_1 @ (k7_relat_1 @ X14 @ X15) @ X15)
% 29.84/30.08          | ~ (v4_relat_1 @ X14 @ X16)
% 29.84/30.08          | ~ (v1_relat_1 @ X14))),
% 29.84/30.08      inference('cnf', [status(esa)], [fc23_relat_1])).
% 29.84/30.08  thf('96', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         (~ (v1_relat_1 @ sk_D) | (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0))),
% 29.84/30.08      inference('sup-', [status(thm)], ['94', '95'])).
% 29.84/30.08  thf('97', plain, ((v1_relat_1 @ sk_D)),
% 29.84/30.08      inference('demod', [status(thm)], ['76', '77'])).
% 29.84/30.08  thf('98', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0)),
% 29.84/30.08      inference('demod', [status(thm)], ['96', '97'])).
% 29.84/30.08  thf('99', plain,
% 29.84/30.08      (![X12 : $i, X13 : $i]:
% 29.84/30.08         (~ (v4_relat_1 @ X12 @ X13)
% 29.84/30.08          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 29.84/30.08          | ~ (v1_relat_1 @ X12))),
% 29.84/30.08      inference('cnf', [status(esa)], [d18_relat_1])).
% 29.84/30.08  thf('100', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 29.84/30.08          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0))),
% 29.84/30.08      inference('sup-', [status(thm)], ['98', '99'])).
% 29.84/30.08  thf('101', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 29.84/30.08      inference('sup-', [status(thm)], ['92', '93'])).
% 29.84/30.08  thf('102', plain,
% 29.84/30.08      (![X14 : $i, X15 : $i, X16 : $i]:
% 29.84/30.08         ((v1_relat_1 @ (k7_relat_1 @ X14 @ X15))
% 29.84/30.08          | ~ (v4_relat_1 @ X14 @ X16)
% 29.84/30.08          | ~ (v1_relat_1 @ X14))),
% 29.84/30.08      inference('cnf', [status(esa)], [fc23_relat_1])).
% 29.84/30.08  thf('103', plain,
% 29.84/30.08      (![X0 : $i]:
% 29.84/30.08         (~ (v1_relat_1 @ sk_D) | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 29.84/30.08      inference('sup-', [status(thm)], ['101', '102'])).
% 29.84/30.08  thf('104', plain, ((v1_relat_1 @ sk_D)),
% 29.84/30.08      inference('demod', [status(thm)], ['76', '77'])).
% 29.84/30.08  thf('105', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 29.84/30.09      inference('demod', [status(thm)], ['103', '104'])).
% 29.84/30.09  thf('106', plain,
% 29.84/30.09      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0)),
% 29.84/30.09      inference('demod', [status(thm)], ['100', '105'])).
% 29.84/30.09  thf('107', plain,
% 29.84/30.09      (((r1_tarski @ sk_C @ sk_C))
% 29.84/30.09         <= (~
% 29.84/30.09             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.09               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 29.84/30.09      inference('sup+', [status(thm)], ['91', '106'])).
% 29.84/30.09  thf('108', plain,
% 29.84/30.09      ((((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C)))
% 29.84/30.09         <= (~
% 29.84/30.09             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.09               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['18', '90'])).
% 29.84/30.09  thf('109', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 29.84/30.09      inference('sup-', [status(thm)], ['92', '93'])).
% 29.84/30.09  thf('110', plain,
% 29.84/30.09      (![X19 : $i, X20 : $i]:
% 29.84/30.09         (((X19) = (k7_relat_1 @ X19 @ X20))
% 29.84/30.09          | ~ (v4_relat_1 @ X19 @ X20)
% 29.84/30.09          | ~ (v1_relat_1 @ X19))),
% 29.84/30.09      inference('cnf', [status(esa)], [t209_relat_1])).
% 29.84/30.09  thf('111', plain,
% 29.84/30.09      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_A)))),
% 29.84/30.09      inference('sup-', [status(thm)], ['109', '110'])).
% 29.84/30.09  thf('112', plain, ((v1_relat_1 @ sk_D)),
% 29.84/30.09      inference('demod', [status(thm)], ['76', '77'])).
% 29.84/30.09  thf('113', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 29.84/30.09      inference('demod', [status(thm)], ['111', '112'])).
% 29.84/30.09  thf('114', plain,
% 29.84/30.09      (![X21 : $i, X22 : $i]:
% 29.84/30.09         ((r1_tarski @ (k7_relat_1 @ X21 @ X22) @ X21) | ~ (v1_relat_1 @ X21))),
% 29.84/30.09      inference('cnf', [status(esa)], [t88_relat_1])).
% 29.84/30.09  thf('115', plain, (((r1_tarski @ sk_D @ sk_D) | ~ (v1_relat_1 @ sk_D))),
% 29.84/30.09      inference('sup+', [status(thm)], ['113', '114'])).
% 29.84/30.09  thf('116', plain, ((v1_relat_1 @ sk_D)),
% 29.84/30.09      inference('demod', [status(thm)], ['76', '77'])).
% 29.84/30.09  thf('117', plain, ((r1_tarski @ sk_D @ sk_D)),
% 29.84/30.09      inference('demod', [status(thm)], ['115', '116'])).
% 29.84/30.09  thf('118', plain,
% 29.84/30.09      (![X21 : $i, X22 : $i]:
% 29.84/30.09         ((r1_tarski @ (k7_relat_1 @ X21 @ X22) @ X21) | ~ (v1_relat_1 @ X21))),
% 29.84/30.09      inference('cnf', [status(esa)], [t88_relat_1])).
% 29.84/30.09  thf('119', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.84/30.09         (~ (r1_tarski @ X0 @ X1)
% 29.84/30.09          | ~ (r1_tarski @ X1 @ X2)
% 29.84/30.09          | (r1_tarski @ X0 @ X2))),
% 29.84/30.09      inference('cnf', [status(esa)], [t1_xboole_1])).
% 29.84/30.09  thf('120', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.84/30.09         (~ (v1_relat_1 @ X0)
% 29.84/30.09          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 29.84/30.09          | ~ (r1_tarski @ X0 @ X2))),
% 29.84/30.09      inference('sup-', [status(thm)], ['118', '119'])).
% 29.84/30.09  thf('121', plain,
% 29.84/30.09      (![X0 : $i]:
% 29.84/30.09         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ sk_D) | ~ (v1_relat_1 @ sk_D))),
% 29.84/30.09      inference('sup-', [status(thm)], ['117', '120'])).
% 29.84/30.09  thf('122', plain, ((v1_relat_1 @ sk_D)),
% 29.84/30.09      inference('demod', [status(thm)], ['76', '77'])).
% 29.84/30.09  thf('123', plain,
% 29.84/30.09      (![X0 : $i]: (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ sk_D)),
% 29.84/30.09      inference('demod', [status(thm)], ['121', '122'])).
% 29.84/30.09  thf('124', plain,
% 29.84/30.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.09  thf(t4_relset_1, axiom,
% 29.84/30.09    (![A:$i,B:$i,C:$i,D:$i]:
% 29.84/30.09     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 29.84/30.09       ( ( r1_tarski @ A @ D ) =>
% 29.84/30.09         ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 29.84/30.09  thf('125', plain,
% 29.84/30.09      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 29.84/30.09         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 29.84/30.09          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 29.84/30.09          | ~ (r1_tarski @ X35 @ X38))),
% 29.84/30.09      inference('cnf', [status(esa)], [t4_relset_1])).
% 29.84/30.09  thf('126', plain,
% 29.84/30.09      (![X0 : $i]:
% 29.84/30.09         (~ (r1_tarski @ X0 @ sk_D)
% 29.84/30.09          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['124', '125'])).
% 29.84/30.09  thf('127', plain,
% 29.84/30.09      (![X0 : $i]:
% 29.84/30.09         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 29.84/30.09          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 29.84/30.09      inference('sup-', [status(thm)], ['123', '126'])).
% 29.84/30.09  thf(t13_relset_1, axiom,
% 29.84/30.09    (![A:$i,B:$i,C:$i,D:$i]:
% 29.84/30.09     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 29.84/30.09       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 29.84/30.09         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 29.84/30.09  thf('128', plain,
% 29.84/30.09      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 29.84/30.09         (~ (r1_tarski @ (k1_relat_1 @ X31) @ X32)
% 29.84/30.09          | (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 29.84/30.09          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 29.84/30.09      inference('cnf', [status(esa)], [t13_relset_1])).
% 29.84/30.09  thf('129', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i]:
% 29.84/30.09         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 29.84/30.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 29.84/30.09          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 29.84/30.09      inference('sup-', [status(thm)], ['127', '128'])).
% 29.84/30.09  thf('130', plain,
% 29.84/30.09      ((![X0 : $i]:
% 29.84/30.09          (~ (r1_tarski @ sk_C @ X0)
% 29.84/30.09           | (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 29.84/30.09              (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))))
% 29.84/30.09         <= (~
% 29.84/30.09             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.09               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['108', '129'])).
% 29.84/30.09  thf('131', plain,
% 29.84/30.09      (((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 29.84/30.09         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 29.84/30.09         <= (~
% 29.84/30.09             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.09               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['107', '130'])).
% 29.84/30.09  thf('132', plain,
% 29.84/30.09      (((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.09         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 29.84/30.09      inference('demod', [status(thm)], ['17', '131'])).
% 29.84/30.09  thf('133', plain,
% 29.84/30.09      (~
% 29.84/30.09       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)) | 
% 29.84/30.09       ~
% 29.84/30.09       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.09         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) | 
% 29.84/30.09       ~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 29.84/30.09      inference('split', [status(esa)], ['0'])).
% 29.84/30.09  thf('134', plain,
% 29.84/30.09      (~
% 29.84/30.09       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 29.84/30.09      inference('sat_resolution*', [status(thm)], ['14', '132', '133'])).
% 29.84/30.09  thf('135', plain,
% 29.84/30.09      (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 29.84/30.09      inference('simpl_trail', [status(thm)], ['7', '134'])).
% 29.84/30.09  thf('136', plain, ((r1_tarski @ sk_C @ sk_A)),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.09  thf('137', plain,
% 29.84/30.09      (![X39 : $i, X40 : $i]:
% 29.84/30.09         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 29.84/30.09  thf('138', plain,
% 29.84/30.09      (![X39 : $i, X40 : $i]:
% 29.84/30.09         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 29.84/30.09  thf('139', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.84/30.09         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 29.84/30.09      inference('sup+', [status(thm)], ['137', '138'])).
% 29.84/30.09  thf('140', plain,
% 29.84/30.09      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 29.84/30.09      inference('sup-', [status(thm)], ['23', '24'])).
% 29.84/30.09  thf('141', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i]:
% 29.84/30.09         ((zip_tseitin_0 @ X1 @ X0)
% 29.84/30.09          | ((sk_B) = (X1))
% 29.84/30.09          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 29.84/30.09      inference('sup-', [status(thm)], ['139', '140'])).
% 29.84/30.09  thf('142', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.09  thf('143', plain,
% 29.84/30.09      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 29.84/30.09      inference('split', [status(esa)], ['142'])).
% 29.84/30.09  thf('144', plain,
% 29.84/30.09      ((![X0 : $i, X1 : $i]:
% 29.84/30.09          (((X0) != (k1_xboole_0))
% 29.84/30.09           | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 29.84/30.09           | (zip_tseitin_0 @ X0 @ X1)))
% 29.84/30.09         <= (~ (((sk_B) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['141', '143'])).
% 29.84/30.09  thf('145', plain,
% 29.84/30.09      ((![X1 : $i]:
% 29.84/30.09          ((zip_tseitin_0 @ k1_xboole_0 @ X1)
% 29.84/30.09           | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)))
% 29.84/30.09         <= (~ (((sk_B) = (k1_xboole_0))))),
% 29.84/30.09      inference('simplify', [status(thm)], ['144'])).
% 29.84/30.09  thf('146', plain,
% 29.84/30.09      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 29.84/30.09      inference('demod', [status(thm)], ['29', '32'])).
% 29.84/30.09  thf('147', plain,
% 29.84/30.09      ((![X0 : $i]:
% 29.84/30.09          ((zip_tseitin_0 @ k1_xboole_0 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D))))
% 29.84/30.09         <= (~ (((sk_B) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['145', '146'])).
% 29.84/30.09  thf('148', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 29.84/30.09      inference('demod', [status(thm)], ['62', '65'])).
% 29.84/30.09  thf('149', plain,
% 29.84/30.09      (![X7 : $i, X9 : $i]:
% 29.84/30.09         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 29.84/30.09      inference('cnf', [status(esa)], [t3_subset])).
% 29.84/30.09  thf('150', plain,
% 29.84/30.09      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 29.84/30.09      inference('sup-', [status(thm)], ['148', '149'])).
% 29.84/30.09  thf('151', plain,
% 29.84/30.09      (![X44 : $i, X45 : $i, X46 : $i]:
% 29.84/30.09         (~ (zip_tseitin_0 @ X44 @ X45)
% 29.84/30.09          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 29.84/30.09          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_5])).
% 29.84/30.09  thf('152', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i]:
% 29.84/30.09         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 29.84/30.09      inference('sup-', [status(thm)], ['150', '151'])).
% 29.84/30.09  thf('153', plain,
% 29.84/30.09      ((![X0 : $i]:
% 29.84/30.09          (((sk_A) = (k1_relat_1 @ sk_D))
% 29.84/30.09           | (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)))
% 29.84/30.09         <= (~ (((sk_B) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['147', '152'])).
% 29.84/30.09  thf('154', plain,
% 29.84/30.09      (![X44 : $i, X45 : $i, X46 : $i]:
% 29.84/30.09         (((X44) != (k1_xboole_0))
% 29.84/30.09          | ((X45) = (k1_xboole_0))
% 29.84/30.09          | (v1_funct_2 @ X46 @ X45 @ X44)
% 29.84/30.09          | ((X46) != (k1_xboole_0))
% 29.84/30.09          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_5])).
% 29.84/30.09  thf('155', plain,
% 29.84/30.09      (![X45 : $i]:
% 29.84/30.09         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 29.84/30.09             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ k1_xboole_0)))
% 29.84/30.09          | (v1_funct_2 @ k1_xboole_0 @ X45 @ k1_xboole_0)
% 29.84/30.09          | ((X45) = (k1_xboole_0)))),
% 29.84/30.09      inference('simplify', [status(thm)], ['154'])).
% 29.84/30.09  thf('156', plain,
% 29.84/30.09      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 29.84/30.09      inference('simplify', [status(thm)], ['20'])).
% 29.84/30.09  thf('157', plain,
% 29.84/30.09      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 29.84/30.09      inference('sup-', [status(thm)], ['148', '149'])).
% 29.84/30.09  thf('158', plain,
% 29.84/30.09      (![X45 : $i]:
% 29.84/30.09         ((v1_funct_2 @ k1_xboole_0 @ X45 @ k1_xboole_0)
% 29.84/30.09          | ((X45) = (k1_xboole_0)))),
% 29.84/30.09      inference('demod', [status(thm)], ['155', '156', '157'])).
% 29.84/30.09  thf('159', plain,
% 29.84/30.09      (![X41 : $i, X42 : $i, X43 : $i]:
% 29.84/30.09         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 29.84/30.09          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 29.84/30.09          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 29.84/30.09  thf('160', plain,
% 29.84/30.09      (![X0 : $i]:
% 29.84/30.09         (((X0) = (k1_xboole_0))
% 29.84/30.09          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 29.84/30.09          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 29.84/30.09      inference('sup-', [status(thm)], ['158', '159'])).
% 29.84/30.09  thf('161', plain,
% 29.84/30.09      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 29.84/30.09      inference('sup-', [status(thm)], ['148', '149'])).
% 29.84/30.09  thf('162', plain,
% 29.84/30.09      (![X28 : $i, X29 : $i, X30 : $i]:
% 29.84/30.09         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 29.84/30.09          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 29.84/30.09      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 29.84/30.09  thf('163', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i]:
% 29.84/30.09         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 29.84/30.09      inference('sup-', [status(thm)], ['161', '162'])).
% 29.84/30.09  thf('164', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 29.84/30.09      inference('sup-', [status(thm)], ['63', '64'])).
% 29.84/30.09  thf('165', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i]:
% 29.84/30.09         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 29.84/30.09      inference('demod', [status(thm)], ['163', '164'])).
% 29.84/30.09  thf('166', plain,
% 29.84/30.09      (![X0 : $i]:
% 29.84/30.09         (((X0) = (k1_xboole_0))
% 29.84/30.09          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 29.84/30.09          | ((X0) = (k1_xboole_0)))),
% 29.84/30.09      inference('demod', [status(thm)], ['160', '165'])).
% 29.84/30.09  thf('167', plain,
% 29.84/30.09      (![X0 : $i]:
% 29.84/30.09         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 29.84/30.09          | ((X0) = (k1_xboole_0)))),
% 29.84/30.09      inference('simplify', [status(thm)], ['166'])).
% 29.84/30.09  thf('168', plain,
% 29.84/30.09      ((![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | ((X0) = (k1_xboole_0))))
% 29.84/30.09         <= (~ (((sk_B) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['153', '167'])).
% 29.84/30.09  thf('169', plain,
% 29.84/30.09      ((![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | ((X0) = (k1_xboole_0))))
% 29.84/30.09         <= (~ (((sk_B) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['153', '167'])).
% 29.84/30.09  thf('170', plain,
% 29.84/30.09      ((![X0 : $i, X1 : $i]:
% 29.84/30.09          (((X1) = (X0))
% 29.84/30.09           | ((sk_A) = (k1_relat_1 @ sk_D))
% 29.84/30.09           | ((sk_A) = (k1_relat_1 @ sk_D))))
% 29.84/30.09         <= (~ (((sk_B) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup+', [status(thm)], ['168', '169'])).
% 29.84/30.09  thf('171', plain,
% 29.84/30.09      ((![X0 : $i, X1 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | ((X1) = (X0))))
% 29.84/30.09         <= (~ (((sk_B) = (k1_xboole_0))))),
% 29.84/30.09      inference('simplify', [status(thm)], ['170'])).
% 29.84/30.09  thf('172', plain,
% 29.84/30.09      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 29.84/30.09      inference('condensation', [status(thm)], ['171'])).
% 29.84/30.09  thf('173', plain,
% 29.84/30.09      (![X23 : $i, X24 : $i]:
% 29.84/30.09         (~ (r1_tarski @ X23 @ (k1_relat_1 @ X24))
% 29.84/30.09          | ((k1_relat_1 @ (k7_relat_1 @ X24 @ X23)) = (X23))
% 29.84/30.09          | ~ (v1_relat_1 @ X24))),
% 29.84/30.09      inference('cnf', [status(esa)], [t91_relat_1])).
% 29.84/30.09  thf('174', plain,
% 29.84/30.09      ((![X0 : $i]:
% 29.84/30.09          (~ (r1_tarski @ X0 @ sk_A)
% 29.84/30.09           | ~ (v1_relat_1 @ sk_D)
% 29.84/30.09           | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0))))
% 29.84/30.09         <= (~ (((sk_B) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['172', '173'])).
% 29.84/30.09  thf('175', plain, ((v1_relat_1 @ sk_D)),
% 29.84/30.09      inference('demod', [status(thm)], ['76', '77'])).
% 29.84/30.09  thf('176', plain,
% 29.84/30.09      ((![X0 : $i]:
% 29.84/30.09          (~ (r1_tarski @ X0 @ sk_A)
% 29.84/30.09           | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0))))
% 29.84/30.09         <= (~ (((sk_B) = (k1_xboole_0))))),
% 29.84/30.09      inference('demod', [status(thm)], ['174', '175'])).
% 29.84/30.09  thf('177', plain,
% 29.84/30.09      ((((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C)))
% 29.84/30.09         <= (~ (((sk_B) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['136', '176'])).
% 29.84/30.09  thf('178', plain,
% 29.84/30.09      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 29.84/30.09      inference('split', [status(esa)], ['142'])).
% 29.84/30.09  thf('179', plain,
% 29.84/30.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.09  thf('180', plain,
% 29.84/30.09      (((m1_subset_1 @ sk_D @ 
% 29.84/30.09         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 29.84/30.09         <= ((((sk_A) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup+', [status(thm)], ['178', '179'])).
% 29.84/30.09  thf('181', plain,
% 29.84/30.09      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 29.84/30.09      inference('simplify', [status(thm)], ['44'])).
% 29.84/30.09  thf('182', plain,
% 29.84/30.09      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 29.84/30.09         <= ((((sk_A) = (k1_xboole_0))))),
% 29.84/30.09      inference('demod', [status(thm)], ['180', '181'])).
% 29.84/30.09  thf('183', plain,
% 29.84/30.09      (![X7 : $i, X8 : $i]:
% 29.84/30.09         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 29.84/30.09      inference('cnf', [status(esa)], [t3_subset])).
% 29.84/30.09  thf('184', plain,
% 29.84/30.09      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['182', '183'])).
% 29.84/30.09  thf('185', plain,
% 29.84/30.09      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 29.84/30.09      inference('cnf', [status(esa)], [t3_xboole_1])).
% 29.84/30.09  thf('186', plain,
% 29.84/30.09      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['184', '185'])).
% 29.84/30.09  thf('187', plain, ((v1_funct_1 @ sk_D)),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.09  thf('188', plain,
% 29.84/30.09      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup+', [status(thm)], ['186', '187'])).
% 29.84/30.09  thf('189', plain,
% 29.84/30.09      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 29.84/30.09      inference('sup-', [status(thm)], ['148', '149'])).
% 29.84/30.09  thf('190', plain,
% 29.84/30.09      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 29.84/30.09         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 29.84/30.09          | ~ (v1_funct_1 @ X51)
% 29.84/30.09          | ((k2_partfun1 @ X52 @ X53 @ X51 @ X54) = (k7_relat_1 @ X51 @ X54)))),
% 29.84/30.09      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 29.84/30.09  thf('191', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.84/30.09         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 29.84/30.09            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 29.84/30.09          | ~ (v1_funct_1 @ k1_xboole_0))),
% 29.84/30.09      inference('sup-', [status(thm)], ['189', '190'])).
% 29.84/30.09  thf('192', plain,
% 29.84/30.09      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 29.84/30.09      inference('demod', [status(thm)], ['43', '47'])).
% 29.84/30.09  thf('193', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.84/30.09         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 29.84/30.09          | ~ (v1_funct_1 @ k1_xboole_0))),
% 29.84/30.09      inference('demod', [status(thm)], ['191', '192'])).
% 29.84/30.09  thf('194', plain,
% 29.84/30.09      ((![X0 : $i, X1 : $i, X2 : $i]:
% 29.84/30.09          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 29.84/30.09         <= ((((sk_A) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['188', '193'])).
% 29.84/30.09  thf('195', plain,
% 29.84/30.09      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['184', '185'])).
% 29.84/30.09  thf('196', plain,
% 29.84/30.09      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 29.84/30.09      inference('split', [status(esa)], ['142'])).
% 29.84/30.09  thf('197', plain,
% 29.84/30.09      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))
% 29.84/30.09         <= (~
% 29.84/30.09             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 29.84/30.09               sk_B)))),
% 29.84/30.09      inference('split', [status(esa)], ['0'])).
% 29.84/30.09  thf('198', plain,
% 29.84/30.09      ((~ (v1_funct_2 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 29.84/30.09           sk_C @ sk_B))
% 29.84/30.09         <= (~
% 29.84/30.09             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 29.84/30.09               sk_B)) & 
% 29.84/30.09             (((sk_A) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['196', '197'])).
% 29.84/30.09  thf('199', plain,
% 29.84/30.09      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 29.84/30.09      inference('split', [status(esa)], ['142'])).
% 29.84/30.09  thf('200', plain, ((r1_tarski @ sk_C @ sk_A)),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.84/30.09  thf('201', plain,
% 29.84/30.09      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup+', [status(thm)], ['199', '200'])).
% 29.84/30.09  thf('202', plain,
% 29.84/30.09      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 29.84/30.09      inference('cnf', [status(esa)], [t3_xboole_1])).
% 29.84/30.09  thf('203', plain,
% 29.84/30.09      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['201', '202'])).
% 29.84/30.09  thf('204', plain,
% 29.84/30.09      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['201', '202'])).
% 29.84/30.09  thf('205', plain,
% 29.84/30.09      ((~ (v1_funct_2 @ 
% 29.84/30.09           (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ k1_xboole_0) @ 
% 29.84/30.09           k1_xboole_0 @ sk_B))
% 29.84/30.09         <= (~
% 29.84/30.09             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 29.84/30.09               sk_B)) & 
% 29.84/30.09             (((sk_A) = (k1_xboole_0))))),
% 29.84/30.09      inference('demod', [status(thm)], ['198', '203', '204'])).
% 29.84/30.09  thf('206', plain,
% 29.84/30.09      ((~ (v1_funct_2 @ 
% 29.84/30.09           (k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0) @ 
% 29.84/30.09           k1_xboole_0 @ sk_B))
% 29.84/30.09         <= (~
% 29.84/30.09             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 29.84/30.09               sk_B)) & 
% 29.84/30.09             (((sk_A) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['195', '205'])).
% 29.84/30.09  thf('207', plain,
% 29.84/30.09      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B))
% 29.84/30.09         <= (~
% 29.84/30.09             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 29.84/30.09               sk_B)) & 
% 29.84/30.09             (((sk_A) = (k1_xboole_0))))),
% 29.84/30.09      inference('sup-', [status(thm)], ['194', '206'])).
% 29.84/30.09  thf('208', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i]:
% 29.84/30.09         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 29.84/30.09      inference('demod', [status(thm)], ['163', '164'])).
% 29.84/30.09  thf('209', plain,
% 29.84/30.09      (![X41 : $i, X42 : $i, X43 : $i]:
% 29.84/30.09         (((X41) != (k1_relset_1 @ X41 @ X42 @ X43))
% 29.84/30.09          | (v1_funct_2 @ X43 @ X41 @ X42)
% 29.84/30.09          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 29.84/30.09  thf('210', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i]:
% 29.84/30.09         (((X1) != (k1_xboole_0))
% 29.84/30.09          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 29.84/30.09          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 29.84/30.09      inference('sup-', [status(thm)], ['208', '209'])).
% 29.84/30.09  thf('211', plain,
% 29.84/30.09      (![X0 : $i]:
% 29.84/30.09         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 29.84/30.09          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 29.84/30.09      inference('simplify', [status(thm)], ['210'])).
% 29.84/30.09  thf('212', plain,
% 29.84/30.09      (![X39 : $i, X40 : $i]:
% 29.84/30.09         ((zip_tseitin_0 @ X39 @ X40) | ((X40) != (k1_xboole_0)))),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 29.84/30.09  thf('213', plain, (![X39 : $i]: (zip_tseitin_0 @ X39 @ k1_xboole_0)),
% 29.84/30.09      inference('simplify', [status(thm)], ['212'])).
% 29.84/30.09  thf('214', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i]:
% 29.84/30.09         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 29.84/30.09      inference('sup-', [status(thm)], ['150', '151'])).
% 29.84/30.09  thf('215', plain,
% 29.84/30.09      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 29.84/30.09      inference('sup-', [status(thm)], ['213', '214'])).
% 29.84/30.09  thf('216', plain,
% 29.84/30.09      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 29.84/30.09      inference('demod', [status(thm)], ['211', '215'])).
% 29.84/30.09  thf('217', plain,
% 29.84/30.09      (~ (((sk_A) = (k1_xboole_0))) | 
% 29.84/30.09       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 29.84/30.09      inference('demod', [status(thm)], ['207', '216'])).
% 29.84/30.09  thf('218', plain,
% 29.84/30.09      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 29.84/30.09      inference('split', [status(esa)], ['142'])).
% 29.84/30.09  thf('219', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 29.84/30.09      inference('sat_resolution*', [status(thm)],
% 29.84/30.09                ['14', '132', '133', '217', '218'])).
% 29.84/30.09  thf('220', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 29.84/30.09      inference('simpl_trail', [status(thm)], ['177', '219'])).
% 29.84/30.09  thf('221', plain,
% 29.84/30.09      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0)),
% 29.84/30.09      inference('demod', [status(thm)], ['100', '105'])).
% 29.84/30.09  thf('222', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i]:
% 29.84/30.09         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 29.84/30.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 29.84/30.09          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 29.84/30.09      inference('sup-', [status(thm)], ['127', '128'])).
% 29.84/30.09  thf('223', plain,
% 29.84/30.09      (![X0 : $i]:
% 29.84/30.09         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 29.84/30.09          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 29.84/30.09      inference('sup-', [status(thm)], ['221', '222'])).
% 29.84/30.09  thf('224', plain,
% 29.84/30.09      (![X28 : $i, X29 : $i, X30 : $i]:
% 29.84/30.09         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 29.84/30.09          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 29.84/30.09      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 29.84/30.09  thf('225', plain,
% 29.84/30.09      (![X0 : $i]:
% 29.84/30.09         ((k1_relset_1 @ X0 @ sk_B @ (k7_relat_1 @ sk_D @ X0))
% 29.84/30.09           = (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 29.84/30.09      inference('sup-', [status(thm)], ['223', '224'])).
% 29.84/30.09  thf('226', plain,
% 29.84/30.09      (![X41 : $i, X42 : $i, X43 : $i]:
% 29.84/30.09         (((X41) != (k1_relset_1 @ X41 @ X42 @ X43))
% 29.84/30.09          | (v1_funct_2 @ X43 @ X41 @ X42)
% 29.84/30.09          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 29.84/30.09  thf('227', plain,
% 29.84/30.09      (![X0 : $i]:
% 29.84/30.09         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 29.84/30.09          | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 29.84/30.09          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 29.84/30.09      inference('sup-', [status(thm)], ['225', '226'])).
% 29.84/30.09  thf('228', plain,
% 29.84/30.09      (![X0 : $i]:
% 29.84/30.09         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 29.84/30.09          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 29.84/30.09      inference('sup-', [status(thm)], ['221', '222'])).
% 29.84/30.09  thf('229', plain,
% 29.84/30.09      (![X44 : $i, X45 : $i, X46 : $i]:
% 29.84/30.09         (~ (zip_tseitin_0 @ X44 @ X45)
% 29.84/30.09          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 29.84/30.09          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_5])).
% 29.84/30.09  thf('230', plain,
% 29.84/30.09      (![X0 : $i]:
% 29.84/30.09         ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 29.84/30.09          | ~ (zip_tseitin_0 @ sk_B @ X0))),
% 29.84/30.09      inference('sup-', [status(thm)], ['228', '229'])).
% 29.84/30.09  thf('231', plain,
% 29.84/30.09      (![X39 : $i, X40 : $i]:
% 29.84/30.09         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 29.84/30.09  thf('232', plain,
% 29.84/30.09      (![X39 : $i, X40 : $i]:
% 29.84/30.09         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 29.84/30.09  thf('233', plain,
% 29.84/30.09      (![X39 : $i, X40 : $i]:
% 29.84/30.09         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 29.84/30.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 29.84/30.09  thf('234', plain,
% 29.84/30.09      (![X45 : $i]:
% 29.84/30.09         ((v1_funct_2 @ k1_xboole_0 @ X45 @ k1_xboole_0)
% 29.84/30.09          | ((X45) = (k1_xboole_0)))),
% 29.84/30.09      inference('demod', [status(thm)], ['155', '156', '157'])).
% 29.84/30.09  thf('235', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.84/30.09         ((v1_funct_2 @ X0 @ X1 @ k1_xboole_0)
% 29.84/30.09          | (zip_tseitin_0 @ X0 @ X2)
% 29.84/30.09          | ((X1) = (k1_xboole_0)))),
% 29.84/30.09      inference('sup+', [status(thm)], ['233', '234'])).
% 29.84/30.09  thf('236', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 29.84/30.09         ((v1_funct_2 @ X2 @ X1 @ X0)
% 29.84/30.09          | (zip_tseitin_0 @ X0 @ X4)
% 29.84/30.09          | ((X1) = (k1_xboole_0))
% 29.84/30.09          | (zip_tseitin_0 @ X2 @ X3))),
% 29.84/30.09      inference('sup+', [status(thm)], ['232', '235'])).
% 29.84/30.09  thf('237', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.84/30.09         ((zip_tseitin_0 @ X1 @ X0)
% 29.84/30.09          | ((X2) = (k1_xboole_0))
% 29.84/30.09          | (v1_funct_2 @ X1 @ X2 @ X1))),
% 29.84/30.09      inference('eq_fact', [status(thm)], ['236'])).
% 29.84/30.09  thf('238', plain,
% 29.84/30.09      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 29.84/30.09      inference('demod', [status(thm)], ['211', '215'])).
% 29.84/30.09  thf('239', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.84/30.09         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1)
% 29.84/30.09          | (v1_funct_2 @ X2 @ X0 @ X2)
% 29.84/30.09          | (zip_tseitin_0 @ X2 @ X3))),
% 29.84/30.09      inference('sup+', [status(thm)], ['237', '238'])).
% 29.84/30.09  thf('240', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i]:
% 29.84/30.09         ((zip_tseitin_0 @ k1_xboole_0 @ X1)
% 29.84/30.09          | (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 29.84/30.09      inference('eq_fact', [status(thm)], ['239'])).
% 29.84/30.09  thf('241', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i]:
% 29.84/30.09         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 29.84/30.09      inference('sup-', [status(thm)], ['150', '151'])).
% 29.84/30.09  thf('242', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i]:
% 29.84/30.09         ((v1_funct_2 @ k1_xboole_0 @ X1 @ k1_xboole_0)
% 29.84/30.09          | (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 29.84/30.09      inference('sup-', [status(thm)], ['240', '241'])).
% 29.84/30.09  thf('243', plain,
% 29.84/30.09      (![X0 : $i]:
% 29.84/30.09         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 29.84/30.09          | ((X0) = (k1_xboole_0)))),
% 29.84/30.09      inference('simplify', [status(thm)], ['166'])).
% 29.84/30.09  thf('244', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i]:
% 29.84/30.09         ((v1_funct_2 @ k1_xboole_0 @ X1 @ k1_xboole_0)
% 29.84/30.09          | ((X0) = (k1_xboole_0)))),
% 29.84/30.09      inference('sup-', [status(thm)], ['242', '243'])).
% 29.84/30.09  thf('245', plain,
% 29.84/30.09      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 29.84/30.09      inference('demod', [status(thm)], ['211', '215'])).
% 29.84/30.09  thf('246', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.84/30.09         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1)
% 29.84/30.09          | (v1_funct_2 @ k1_xboole_0 @ X2 @ k1_xboole_0))),
% 29.84/30.09      inference('sup+', [status(thm)], ['244', '245'])).
% 29.84/30.09  thf('247', plain,
% 29.84/30.09      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 29.84/30.09      inference('condensation', [status(thm)], ['246'])).
% 29.84/30.09  thf('248', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.84/30.09         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 29.84/30.09      inference('sup+', [status(thm)], ['231', '247'])).
% 29.84/30.09  thf('249', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.84/30.09         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 29.84/30.09      inference('sup+', [status(thm)], ['19', '21'])).
% 29.84/30.09  thf('250', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 29.84/30.09      inference('sup-', [status(thm)], ['35', '36'])).
% 29.84/30.09  thf('251', plain,
% 29.84/30.09      (![X0 : $i]:
% 29.84/30.09         ((r1_tarski @ sk_D @ k1_xboole_0) | (zip_tseitin_0 @ sk_B @ X0))),
% 29.84/30.09      inference('sup+', [status(thm)], ['249', '250'])).
% 29.84/30.09  thf('252', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.84/30.09         (~ (v1_relat_1 @ X0)
% 29.84/30.09          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 29.84/30.09          | ~ (r1_tarski @ X0 @ X2))),
% 29.84/30.09      inference('sup-', [status(thm)], ['118', '119'])).
% 29.84/30.09  thf('253', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i]:
% 29.84/30.09         ((zip_tseitin_0 @ sk_B @ X1)
% 29.84/30.09          | (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ k1_xboole_0)
% 29.84/30.09          | ~ (v1_relat_1 @ sk_D))),
% 29.84/30.09      inference('sup-', [status(thm)], ['251', '252'])).
% 29.84/30.09  thf('254', plain, ((v1_relat_1 @ sk_D)),
% 29.84/30.09      inference('demod', [status(thm)], ['76', '77'])).
% 29.84/30.09  thf('255', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i]:
% 29.84/30.09         ((zip_tseitin_0 @ sk_B @ X1)
% 29.84/30.09          | (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ k1_xboole_0))),
% 29.84/30.09      inference('demod', [status(thm)], ['253', '254'])).
% 29.84/30.09  thf('256', plain,
% 29.84/30.09      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 29.84/30.09      inference('cnf', [status(esa)], [t3_xboole_1])).
% 29.84/30.09  thf('257', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i]:
% 29.84/30.09         ((zip_tseitin_0 @ sk_B @ X1)
% 29.84/30.09          | ((k7_relat_1 @ sk_D @ X0) = (k1_xboole_0)))),
% 29.84/30.09      inference('sup-', [status(thm)], ['255', '256'])).
% 29.84/30.09  thf('258', plain,
% 29.84/30.09      (![X0 : $i]:
% 29.84/30.09         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 29.84/30.09      inference('demod', [status(thm)], ['4', '5'])).
% 29.84/30.09  thf('259', plain,
% 29.84/30.09      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))
% 29.84/30.09         <= (~
% 29.84/30.09             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 29.84/30.09               sk_B)))),
% 29.84/30.09      inference('split', [status(esa)], ['0'])).
% 29.84/30.09  thf('260', plain,
% 29.84/30.09      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))
% 29.84/30.09         <= (~
% 29.84/30.09             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 29.84/30.09               sk_B)))),
% 29.84/30.09      inference('sup-', [status(thm)], ['258', '259'])).
% 29.84/30.09  thf('261', plain,
% 29.84/30.09      ((![X0 : $i]:
% 29.84/30.09          (~ (v1_funct_2 @ k1_xboole_0 @ sk_C @ sk_B)
% 29.84/30.09           | (zip_tseitin_0 @ sk_B @ X0)))
% 29.84/30.09         <= (~
% 29.84/30.09             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 29.84/30.09               sk_B)))),
% 29.84/30.09      inference('sup-', [status(thm)], ['257', '260'])).
% 29.84/30.09  thf('262', plain,
% 29.84/30.09      (~
% 29.84/30.09       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 29.84/30.09      inference('sat_resolution*', [status(thm)], ['14', '132', '133'])).
% 29.84/30.09  thf('263', plain,
% 29.84/30.09      (![X0 : $i]:
% 29.84/30.09         (~ (v1_funct_2 @ k1_xboole_0 @ sk_C @ sk_B)
% 29.84/30.09          | (zip_tseitin_0 @ sk_B @ X0))),
% 29.84/30.09      inference('simpl_trail', [status(thm)], ['261', '262'])).
% 29.84/30.09  thf('264', plain,
% 29.84/30.09      (![X0 : $i, X1 : $i]:
% 29.84/30.09         ((zip_tseitin_0 @ sk_B @ X1) | (zip_tseitin_0 @ sk_B @ X0))),
% 29.84/30.09      inference('sup-', [status(thm)], ['248', '263'])).
% 29.84/30.09  thf('265', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 29.84/30.09      inference('condensation', [status(thm)], ['264'])).
% 29.84/30.09  thf('266', plain,
% 29.84/30.09      (![X0 : $i]: (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)),
% 29.84/30.09      inference('demod', [status(thm)], ['230', '265'])).
% 29.84/30.09  thf('267', plain,
% 29.84/30.09      (![X0 : $i]:
% 29.84/30.09         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 29.84/30.09          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 29.84/30.09      inference('demod', [status(thm)], ['227', '266'])).
% 29.84/30.09  thf('268', plain,
% 29.84/30.09      ((((sk_C) != (sk_C))
% 29.84/30.09        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 29.84/30.09      inference('sup-', [status(thm)], ['220', '267'])).
% 29.84/30.09  thf('269', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 29.84/30.09      inference('simplify', [status(thm)], ['268'])).
% 29.84/30.09  thf('270', plain, ($false), inference('demod', [status(thm)], ['135', '269'])).
% 29.84/30.09  
% 29.84/30.09  % SZS output end Refutation
% 29.84/30.09  
% 29.84/30.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
