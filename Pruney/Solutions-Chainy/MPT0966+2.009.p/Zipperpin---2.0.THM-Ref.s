%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WRQhusKP2b

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:06 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 531 expanded)
%              Number of leaves         :   29 ( 158 expanded)
%              Depth                    :   17
%              Number of atoms          :  919 (8999 expanded)
%              Number of equality atoms :   86 ( 622 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

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

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X15 )
      | ( zip_tseitin_1 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_B = X1 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_funct_2 @ X13 @ X11 @ X12 )
      | ( X11
        = ( k1_relset_1 @ X11 @ X12 @ X13 ) )
      | ~ ( zip_tseitin_1 @ X13 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k1_relset_1 @ X4 @ X5 @ X3 )
        = ( k1_relat_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','21'])).

thf('23',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['22'])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('25',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('27',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k2_relset_1 @ X7 @ X8 @ X6 )
        = ( k2_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['28','31'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( v1_funct_2 @ X17 @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['34','37','38'])).

thf('40',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('45',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['28','31'])).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X17 ) @ X18 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['35','36'])).

thf('49',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','50'])).

thf('52',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('55',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_funct_2 @ X13 @ X11 @ X12 )
      | ( X11
        = ( k1_relset_1 @ X11 @ X12 @ X13 ) )
      | ~ ( zip_tseitin_1 @ X13 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X15 )
      | ( zip_tseitin_1 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('63',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('65',plain,(
    ! [X9: $i] :
      ( zip_tseitin_0 @ X9 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','65'])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('68',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k1_relset_1 @ X4 @ X5 @ X3 )
        = ( k1_relat_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('69',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','66','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('72',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('74',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','66','69'])).

thf('79',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['34','37','38'])).

thf('80',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('82',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('86',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['43','53','76','77','84','85'])).

thf('87',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_C ),
    inference(simpl_trail,[status(thm)],['40','86'])).

thf('88',plain,
    ( $false
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1','87'])).

thf('89',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['43','53','76','85','77'])).

thf('90',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['88','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WRQhusKP2b
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:35:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.50/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.69  % Solved by: fo/fo7.sh
% 0.50/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.69  % done 176 iterations in 0.210s
% 0.50/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.69  % SZS output start Refutation
% 0.50/0.69  thf(sk_D_type, type, sk_D: $i).
% 0.50/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.50/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.50/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.50/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.50/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.50/0.69  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.50/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.50/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.69  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.50/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.69  thf(t8_funct_2, conjecture,
% 0.50/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.69     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.50/0.69         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.69       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.50/0.69         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.50/0.69           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.50/0.69             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.50/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.69    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.69        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.50/0.69            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.69          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.50/0.69            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.50/0.69              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.50/0.69                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.50/0.69    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 0.50/0.69  thf('0', plain,
% 0.50/0.69      ((~ (v1_funct_1 @ sk_D)
% 0.50/0.69        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.50/0.69        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('1', plain,
% 0.50/0.69      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.50/0.69         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.50/0.69      inference('split', [status(esa)], ['0'])).
% 0.50/0.69  thf(d1_funct_2, axiom,
% 0.50/0.69    (![A:$i,B:$i,C:$i]:
% 0.50/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.69       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.50/0.69           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.50/0.69             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.50/0.69         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.69           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.50/0.69             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.50/0.69  thf(zf_stmt_1, axiom,
% 0.50/0.69    (![B:$i,A:$i]:
% 0.50/0.69     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.69       ( zip_tseitin_0 @ B @ A ) ))).
% 0.50/0.69  thf('2', plain,
% 0.50/0.69      (![X9 : $i, X10 : $i]:
% 0.50/0.69         ((zip_tseitin_0 @ X9 @ X10) | ((X9) = (k1_xboole_0)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.69  thf('3', plain,
% 0.50/0.69      (![X9 : $i, X10 : $i]:
% 0.50/0.69         ((zip_tseitin_0 @ X9 @ X10) | ((X9) = (k1_xboole_0)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.69  thf('4', plain,
% 0.50/0.69      (![X9 : $i, X10 : $i]:
% 0.50/0.69         ((zip_tseitin_0 @ X9 @ X10) | ((X9) = (k1_xboole_0)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.69  thf('5', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.69         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 0.50/0.69      inference('sup+', [status(thm)], ['3', '4'])).
% 0.50/0.69  thf('6', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.50/0.69  thf(zf_stmt_3, axiom,
% 0.50/0.69    (![C:$i,B:$i,A:$i]:
% 0.50/0.69     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.50/0.69       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.50/0.69  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.50/0.69  thf(zf_stmt_5, axiom,
% 0.50/0.69    (![A:$i,B:$i,C:$i]:
% 0.50/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.69       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.50/0.69         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.50/0.69           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.50/0.69             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.50/0.69  thf('7', plain,
% 0.50/0.69      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.50/0.69         (~ (zip_tseitin_0 @ X14 @ X15)
% 0.50/0.69          | (zip_tseitin_1 @ X16 @ X14 @ X15)
% 0.50/0.69          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14))))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.50/0.69  thf('8', plain,
% 0.50/0.69      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['6', '7'])).
% 0.50/0.69  thf('9', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]:
% 0.50/0.69         ((zip_tseitin_0 @ X1 @ X0)
% 0.50/0.69          | ((sk_B) = (X1))
% 0.50/0.69          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['5', '8'])).
% 0.50/0.69  thf('10', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('11', plain,
% 0.50/0.69      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.50/0.69      inference('split', [status(esa)], ['10'])).
% 0.50/0.69  thf('12', plain,
% 0.50/0.69      ((![X0 : $i, X1 : $i]:
% 0.50/0.69          (((X0) != (k1_xboole_0))
% 0.50/0.69           | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.50/0.69           | (zip_tseitin_0 @ X0 @ X1)))
% 0.50/0.69         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['9', '11'])).
% 0.50/0.69  thf('13', plain,
% 0.50/0.69      ((![X1 : $i]:
% 0.50/0.69          ((zip_tseitin_0 @ k1_xboole_0 @ X1)
% 0.50/0.69           | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)))
% 0.50/0.69         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.50/0.69      inference('simplify', [status(thm)], ['12'])).
% 0.50/0.69  thf('14', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('15', plain,
% 0.50/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.50/0.69         (~ (v1_funct_2 @ X13 @ X11 @ X12)
% 0.50/0.69          | ((X11) = (k1_relset_1 @ X11 @ X12 @ X13))
% 0.50/0.69          | ~ (zip_tseitin_1 @ X13 @ X12 @ X11))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.69  thf('16', plain,
% 0.50/0.69      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.50/0.69        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['14', '15'])).
% 0.50/0.69  thf('17', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf(redefinition_k1_relset_1, axiom,
% 0.50/0.69    (![A:$i,B:$i,C:$i]:
% 0.50/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.69       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.50/0.69  thf('18', plain,
% 0.50/0.69      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.50/0.69         (((k1_relset_1 @ X4 @ X5 @ X3) = (k1_relat_1 @ X3))
% 0.50/0.69          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.50/0.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.50/0.69  thf('19', plain,
% 0.50/0.69      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.50/0.69      inference('sup-', [status(thm)], ['17', '18'])).
% 0.50/0.69  thf('20', plain,
% 0.50/0.69      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.50/0.69      inference('demod', [status(thm)], ['16', '19'])).
% 0.50/0.69  thf('21', plain,
% 0.50/0.69      ((![X0 : $i]:
% 0.50/0.69          ((zip_tseitin_0 @ k1_xboole_0 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D))))
% 0.50/0.69         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['13', '20'])).
% 0.50/0.69  thf('22', plain,
% 0.50/0.69      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.69          ((zip_tseitin_0 @ X0 @ X1)
% 0.50/0.69           | (zip_tseitin_0 @ X0 @ X2)
% 0.50/0.69           | ((sk_A) = (k1_relat_1 @ sk_D))))
% 0.50/0.69         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.50/0.69      inference('sup+', [status(thm)], ['2', '21'])).
% 0.50/0.69  thf('23', plain,
% 0.50/0.69      ((![X0 : $i, X1 : $i]:
% 0.50/0.69          (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ X1 @ X0)))
% 0.50/0.69         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.50/0.69      inference('condensation', [status(thm)], ['22'])).
% 0.50/0.69  thf('24', plain,
% 0.50/0.69      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['6', '7'])).
% 0.50/0.69  thf('25', plain,
% 0.50/0.69      (((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)))
% 0.50/0.69         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['23', '24'])).
% 0.50/0.69  thf('26', plain,
% 0.50/0.69      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.50/0.69      inference('demod', [status(thm)], ['16', '19'])).
% 0.50/0.69  thf('27', plain,
% 0.50/0.69      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.50/0.69      inference('clc', [status(thm)], ['25', '26'])).
% 0.50/0.69  thf('28', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('29', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf(redefinition_k2_relset_1, axiom,
% 0.50/0.69    (![A:$i,B:$i,C:$i]:
% 0.50/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.69       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.50/0.69  thf('30', plain,
% 0.50/0.69      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.50/0.69         (((k2_relset_1 @ X7 @ X8 @ X6) = (k2_relat_1 @ X6))
% 0.50/0.69          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.50/0.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.50/0.69  thf('31', plain,
% 0.50/0.69      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.50/0.69      inference('sup-', [status(thm)], ['29', '30'])).
% 0.50/0.69  thf('32', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.50/0.69      inference('demod', [status(thm)], ['28', '31'])).
% 0.50/0.69  thf(t4_funct_2, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.50/0.69       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.50/0.69         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.50/0.69           ( m1_subset_1 @
% 0.50/0.69             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.50/0.69  thf('33', plain,
% 0.50/0.69      (![X17 : $i, X18 : $i]:
% 0.50/0.69         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 0.50/0.69          | (v1_funct_2 @ X17 @ (k1_relat_1 @ X17) @ X18)
% 0.50/0.69          | ~ (v1_funct_1 @ X17)
% 0.50/0.69          | ~ (v1_relat_1 @ X17))),
% 0.50/0.69      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.50/0.69  thf('34', plain,
% 0.50/0.69      ((~ (v1_relat_1 @ sk_D)
% 0.50/0.69        | ~ (v1_funct_1 @ sk_D)
% 0.50/0.69        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C))),
% 0.50/0.69      inference('sup-', [status(thm)], ['32', '33'])).
% 0.50/0.69  thf('35', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf(cc1_relset_1, axiom,
% 0.50/0.69    (![A:$i,B:$i,C:$i]:
% 0.50/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.69       ( v1_relat_1 @ C ) ))).
% 0.50/0.69  thf('36', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.69         ((v1_relat_1 @ X0)
% 0.50/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 0.50/0.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.50/0.69  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.50/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.50/0.69  thf('38', plain, ((v1_funct_1 @ sk_D)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('39', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.50/0.69      inference('demod', [status(thm)], ['34', '37', '38'])).
% 0.50/0.69  thf('40', plain,
% 0.50/0.69      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.50/0.69      inference('sup+', [status(thm)], ['27', '39'])).
% 0.50/0.69  thf('41', plain, ((v1_funct_1 @ sk_D)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('42', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.50/0.69      inference('split', [status(esa)], ['0'])).
% 0.50/0.69  thf('43', plain, (((v1_funct_1 @ sk_D))),
% 0.50/0.69      inference('sup-', [status(thm)], ['41', '42'])).
% 0.50/0.69  thf('44', plain,
% 0.50/0.69      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.50/0.69      inference('clc', [status(thm)], ['25', '26'])).
% 0.50/0.69  thf('45', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.50/0.69      inference('demod', [status(thm)], ['28', '31'])).
% 0.50/0.69  thf('46', plain,
% 0.50/0.69      (![X17 : $i, X18 : $i]:
% 0.50/0.69         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 0.50/0.69          | (m1_subset_1 @ X17 @ 
% 0.50/0.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X17) @ X18)))
% 0.50/0.69          | ~ (v1_funct_1 @ X17)
% 0.50/0.69          | ~ (v1_relat_1 @ X17))),
% 0.50/0.69      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.50/0.69  thf('47', plain,
% 0.50/0.69      ((~ (v1_relat_1 @ sk_D)
% 0.50/0.69        | ~ (v1_funct_1 @ sk_D)
% 0.50/0.69        | (m1_subset_1 @ sk_D @ 
% 0.50/0.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.69  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 0.50/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.50/0.69  thf('49', plain, ((v1_funct_1 @ sk_D)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('50', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_D @ 
% 0.50/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 0.50/0.69      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.50/0.69  thf('51', plain,
% 0.50/0.69      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.50/0.69         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.50/0.69      inference('sup+', [status(thm)], ['44', '50'])).
% 0.50/0.69  thf('52', plain,
% 0.50/0.69      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.50/0.69         <= (~
% 0.50/0.69             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.50/0.69      inference('split', [status(esa)], ['0'])).
% 0.50/0.69  thf('53', plain,
% 0.50/0.69      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.50/0.69       (((sk_B) = (k1_xboole_0)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['51', '52'])).
% 0.50/0.69  thf('54', plain,
% 0.50/0.69      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.69      inference('split', [status(esa)], ['10'])).
% 0.50/0.69  thf('55', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('56', plain,
% 0.50/0.69      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.50/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.69      inference('sup+', [status(thm)], ['54', '55'])).
% 0.50/0.69  thf('57', plain,
% 0.50/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.50/0.69         (~ (v1_funct_2 @ X13 @ X11 @ X12)
% 0.50/0.69          | ((X11) = (k1_relset_1 @ X11 @ X12 @ X13))
% 0.50/0.69          | ~ (zip_tseitin_1 @ X13 @ X12 @ X11))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.69  thf('58', plain,
% 0.50/0.69      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.50/0.69         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 0.50/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['56', '57'])).
% 0.50/0.69  thf('59', plain,
% 0.50/0.69      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.69      inference('split', [status(esa)], ['10'])).
% 0.50/0.69  thf('60', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('61', plain,
% 0.50/0.69      (((m1_subset_1 @ sk_D @ 
% 0.50/0.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.50/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.69      inference('sup+', [status(thm)], ['59', '60'])).
% 0.50/0.69  thf('62', plain,
% 0.50/0.69      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.50/0.69         (~ (zip_tseitin_0 @ X14 @ X15)
% 0.50/0.69          | (zip_tseitin_1 @ X16 @ X14 @ X15)
% 0.50/0.69          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14))))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.50/0.69  thf('63', plain,
% 0.50/0.69      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.50/0.69         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.50/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['61', '62'])).
% 0.50/0.69  thf('64', plain,
% 0.50/0.69      (![X9 : $i, X10 : $i]:
% 0.50/0.69         ((zip_tseitin_0 @ X9 @ X10) | ((X10) != (k1_xboole_0)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.69  thf('65', plain, (![X9 : $i]: (zip_tseitin_0 @ X9 @ k1_xboole_0)),
% 0.50/0.69      inference('simplify', [status(thm)], ['64'])).
% 0.50/0.69  thf('66', plain,
% 0.50/0.69      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 0.50/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.69      inference('demod', [status(thm)], ['63', '65'])).
% 0.50/0.69  thf('67', plain,
% 0.50/0.69      (((m1_subset_1 @ sk_D @ 
% 0.50/0.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.50/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.69      inference('sup+', [status(thm)], ['59', '60'])).
% 0.50/0.69  thf('68', plain,
% 0.50/0.69      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.50/0.69         (((k1_relset_1 @ X4 @ X5 @ X3) = (k1_relat_1 @ X3))
% 0.50/0.69          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.50/0.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.50/0.69  thf('69', plain,
% 0.50/0.69      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.50/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['67', '68'])).
% 0.50/0.69  thf('70', plain,
% 0.50/0.69      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.69      inference('demod', [status(thm)], ['58', '66', '69'])).
% 0.50/0.69  thf('71', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_D @ 
% 0.50/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 0.50/0.69      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.50/0.69  thf('72', plain,
% 0.50/0.69      (((m1_subset_1 @ sk_D @ 
% 0.50/0.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.50/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.69      inference('sup+', [status(thm)], ['70', '71'])).
% 0.50/0.69  thf('73', plain,
% 0.50/0.69      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.69      inference('split', [status(esa)], ['10'])).
% 0.50/0.69  thf('74', plain,
% 0.50/0.69      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.50/0.69         <= (~
% 0.50/0.69             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.50/0.69      inference('split', [status(esa)], ['0'])).
% 0.50/0.69  thf('75', plain,
% 0.50/0.69      ((~ (m1_subset_1 @ sk_D @ 
% 0.50/0.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.50/0.69         <= (~
% 0.50/0.69             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.50/0.69             (((sk_A) = (k1_xboole_0))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['73', '74'])).
% 0.50/0.69  thf('76', plain,
% 0.50/0.69      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.50/0.69       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['72', '75'])).
% 0.50/0.69  thf('77', plain,
% 0.50/0.69      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.50/0.69       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.50/0.69       ~ ((v1_funct_1 @ sk_D))),
% 0.50/0.69      inference('split', [status(esa)], ['0'])).
% 0.50/0.69  thf('78', plain,
% 0.50/0.69      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.69      inference('demod', [status(thm)], ['58', '66', '69'])).
% 0.50/0.69  thf('79', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.50/0.69      inference('demod', [status(thm)], ['34', '37', '38'])).
% 0.50/0.69  thf('80', plain,
% 0.50/0.69      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.50/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.69      inference('sup+', [status(thm)], ['78', '79'])).
% 0.50/0.69  thf('81', plain,
% 0.50/0.69      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.69      inference('split', [status(esa)], ['10'])).
% 0.50/0.69  thf('82', plain,
% 0.50/0.69      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.50/0.69         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.50/0.69      inference('split', [status(esa)], ['0'])).
% 0.50/0.69  thf('83', plain,
% 0.50/0.69      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.50/0.69         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['81', '82'])).
% 0.50/0.69  thf('84', plain,
% 0.50/0.69      (~ (((sk_A) = (k1_xboole_0))) | ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.50/0.69      inference('sup-', [status(thm)], ['80', '83'])).
% 0.50/0.69  thf('85', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.50/0.69      inference('split', [status(esa)], ['10'])).
% 0.50/0.69  thf('86', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.50/0.69      inference('sat_resolution*', [status(thm)],
% 0.50/0.69                ['43', '53', '76', '77', '84', '85'])).
% 0.50/0.69  thf('87', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.50/0.69      inference('simpl_trail', [status(thm)], ['40', '86'])).
% 0.50/0.69  thf('88', plain, (($false) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.50/0.69      inference('demod', [status(thm)], ['1', '87'])).
% 0.50/0.69  thf('89', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.50/0.69      inference('sat_resolution*', [status(thm)],
% 0.50/0.69                ['43', '53', '76', '85', '77'])).
% 0.50/0.69  thf('90', plain, ($false),
% 0.50/0.69      inference('simpl_trail', [status(thm)], ['88', '89'])).
% 0.50/0.69  
% 0.50/0.69  % SZS output end Refutation
% 0.50/0.69  
% 0.50/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
