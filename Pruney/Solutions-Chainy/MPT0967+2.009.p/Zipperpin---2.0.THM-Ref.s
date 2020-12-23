%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lyazmVvPxX

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:12 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 495 expanded)
%              Number of leaves         :   35 ( 154 expanded)
%              Depth                    :   16
%              Number of atoms          :  845 (7108 expanded)
%              Number of equality atoms :   67 ( 414 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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

thf('5',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,
    ( ( v4_relat_1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v4_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('12',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','15'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('17',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('28',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['26','27'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['21','30'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X29 )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X28 ) @ X29 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','36'])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('39',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('43',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['21','30'])).

thf('44',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X29 )
      | ( v1_funct_2 @ X28 @ ( k1_relat_1 @ X28 ) @ X29 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','48'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('51',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

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

thf('55',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('62',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('64',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('65',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('69',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('73',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['4','41','53','54','74','75'])).

thf('77',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','76'])).

thf('78',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('82',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','41','53','75','54'])).

thf('83',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['80','83'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['77','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lyazmVvPxX
% 0.14/0.37  % Computer   : n010.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 15:59:29 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.77/0.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.95  % Solved by: fo/fo7.sh
% 0.77/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.95  % done 477 iterations in 0.464s
% 0.77/0.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.95  % SZS output start Refutation
% 0.77/0.95  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.77/0.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.77/0.95  thf(sk_D_type, type, sk_D: $i).
% 0.77/0.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.77/0.95  thf(sk_C_type, type, sk_C: $i).
% 0.77/0.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.95  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.77/0.95  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.77/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.77/0.95  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.77/0.95  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.77/0.95  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.77/0.95  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.77/0.95  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.77/0.95  thf(t9_funct_2, conjecture,
% 0.77/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.95     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.77/0.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.77/0.95       ( ( r1_tarski @ B @ C ) =>
% 0.77/0.95         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.77/0.95           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.77/0.95             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.77/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.95    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.95        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.77/0.95            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.77/0.95          ( ( r1_tarski @ B @ C ) =>
% 0.77/0.95            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.77/0.95              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.77/0.95                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.77/0.95    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.77/0.95  thf('0', plain,
% 0.77/0.95      ((~ (v1_funct_1 @ sk_D)
% 0.77/0.95        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.77/0.95        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('1', plain,
% 0.77/0.95      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.77/0.95         <= (~
% 0.77/0.95             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.77/0.95      inference('split', [status(esa)], ['0'])).
% 0.77/0.95  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.77/0.95      inference('split', [status(esa)], ['0'])).
% 0.77/0.95  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.77/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.77/0.95  thf('5', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('6', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.77/0.95      inference('split', [status(esa)], ['5'])).
% 0.77/0.95  thf('7', plain,
% 0.77/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('8', plain,
% 0.77/0.95      (((m1_subset_1 @ sk_D @ 
% 0.77/0.95         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.77/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.77/0.95      inference('sup+', [status(thm)], ['6', '7'])).
% 0.77/0.95  thf(cc2_relset_1, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i]:
% 0.77/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.95       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.77/0.95  thf('9', plain,
% 0.77/0.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.77/0.95         ((v4_relat_1 @ X14 @ X15)
% 0.77/0.95          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.77/0.95      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.77/0.95  thf('10', plain,
% 0.77/0.95      (((v4_relat_1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['8', '9'])).
% 0.77/0.95  thf(d18_relat_1, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( v1_relat_1 @ B ) =>
% 0.77/0.95       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.77/0.95  thf('11', plain,
% 0.77/0.95      (![X7 : $i, X8 : $i]:
% 0.77/0.95         (~ (v4_relat_1 @ X7 @ X8)
% 0.77/0.95          | (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.77/0.95          | ~ (v1_relat_1 @ X7))),
% 0.77/0.95      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.77/0.95  thf('12', plain,
% 0.77/0.95      (((~ (v1_relat_1 @ sk_D)
% 0.77/0.95         | (r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0)))
% 0.77/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['10', '11'])).
% 0.77/0.95  thf('13', plain,
% 0.77/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf(cc1_relset_1, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i]:
% 0.77/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.95       ( v1_relat_1 @ C ) ))).
% 0.77/0.95  thf('14', plain,
% 0.77/0.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.77/0.95         ((v1_relat_1 @ X11)
% 0.77/0.95          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.77/0.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.77/0.95  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.77/0.95      inference('sup-', [status(thm)], ['13', '14'])).
% 0.77/0.95  thf('16', plain,
% 0.77/0.95      (((r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0))
% 0.77/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.77/0.95      inference('demod', [status(thm)], ['12', '15'])).
% 0.77/0.95  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.77/0.95  thf('17', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.77/0.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.77/0.95  thf(d10_xboole_0, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.77/0.95  thf('18', plain,
% 0.77/0.95      (![X0 : $i, X2 : $i]:
% 0.77/0.95         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.77/0.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/0.95  thf('19', plain,
% 0.77/0.95      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['17', '18'])).
% 0.77/0.95  thf('20', plain,
% 0.77/0.95      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['16', '19'])).
% 0.77/0.95  thf('21', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('22', plain,
% 0.77/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('23', plain,
% 0.77/0.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.77/0.95         ((v5_relat_1 @ X14 @ X16)
% 0.77/0.95          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.77/0.95      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.77/0.95  thf('24', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.77/0.95      inference('sup-', [status(thm)], ['22', '23'])).
% 0.77/0.95  thf(d19_relat_1, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( v1_relat_1 @ B ) =>
% 0.77/0.95       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.77/0.95  thf('25', plain,
% 0.77/0.95      (![X9 : $i, X10 : $i]:
% 0.77/0.95         (~ (v5_relat_1 @ X9 @ X10)
% 0.77/0.95          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.77/0.95          | ~ (v1_relat_1 @ X9))),
% 0.77/0.95      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.77/0.95  thf('26', plain,
% 0.77/0.95      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.77/0.95      inference('sup-', [status(thm)], ['24', '25'])).
% 0.77/0.95  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.77/0.95      inference('sup-', [status(thm)], ['13', '14'])).
% 0.77/0.95  thf('28', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.77/0.95      inference('demod', [status(thm)], ['26', '27'])).
% 0.77/0.95  thf(t1_xboole_1, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i]:
% 0.77/0.95     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.77/0.95       ( r1_tarski @ A @ C ) ))).
% 0.77/0.95  thf('29', plain,
% 0.77/0.95      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.77/0.95         (~ (r1_tarski @ X3 @ X4)
% 0.77/0.95          | ~ (r1_tarski @ X4 @ X5)
% 0.77/0.95          | (r1_tarski @ X3 @ X5))),
% 0.77/0.95      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.77/0.95  thf('30', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.77/0.95      inference('sup-', [status(thm)], ['28', '29'])).
% 0.77/0.95  thf('31', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.77/0.95      inference('sup-', [status(thm)], ['21', '30'])).
% 0.77/0.95  thf(t4_funct_2, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.77/0.95       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.77/0.95         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.77/0.95           ( m1_subset_1 @
% 0.77/0.95             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.77/0.95  thf('32', plain,
% 0.77/0.95      (![X28 : $i, X29 : $i]:
% 0.77/0.95         (~ (r1_tarski @ (k2_relat_1 @ X28) @ X29)
% 0.77/0.95          | (m1_subset_1 @ X28 @ 
% 0.77/0.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X28) @ X29)))
% 0.77/0.95          | ~ (v1_funct_1 @ X28)
% 0.77/0.95          | ~ (v1_relat_1 @ X28))),
% 0.77/0.95      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.77/0.95  thf('33', plain,
% 0.77/0.95      ((~ (v1_relat_1 @ sk_D)
% 0.77/0.95        | ~ (v1_funct_1 @ sk_D)
% 0.77/0.95        | (m1_subset_1 @ sk_D @ 
% 0.77/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['31', '32'])).
% 0.77/0.95  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 0.77/0.95      inference('sup-', [status(thm)], ['13', '14'])).
% 0.77/0.95  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('36', plain,
% 0.77/0.95      ((m1_subset_1 @ sk_D @ 
% 0.77/0.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 0.77/0.95      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.77/0.95  thf('37', plain,
% 0.77/0.95      (((m1_subset_1 @ sk_D @ 
% 0.77/0.95         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.77/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.77/0.95      inference('sup+', [status(thm)], ['20', '36'])).
% 0.77/0.95  thf('38', plain,
% 0.77/0.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.77/0.95      inference('split', [status(esa)], ['5'])).
% 0.77/0.95  thf('39', plain,
% 0.77/0.95      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.77/0.95         <= (~
% 0.77/0.95             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.77/0.95      inference('split', [status(esa)], ['0'])).
% 0.77/0.95  thf('40', plain,
% 0.77/0.95      ((~ (m1_subset_1 @ sk_D @ 
% 0.77/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.77/0.95         <= (~
% 0.77/0.95             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.77/0.95             (((sk_A) = (k1_xboole_0))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['38', '39'])).
% 0.77/0.95  thf('41', plain,
% 0.77/0.95      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.77/0.95       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['37', '40'])).
% 0.77/0.95  thf('42', plain,
% 0.77/0.95      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['16', '19'])).
% 0.77/0.95  thf('43', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.77/0.95      inference('sup-', [status(thm)], ['21', '30'])).
% 0.77/0.95  thf('44', plain,
% 0.77/0.95      (![X28 : $i, X29 : $i]:
% 0.77/0.95         (~ (r1_tarski @ (k2_relat_1 @ X28) @ X29)
% 0.77/0.95          | (v1_funct_2 @ X28 @ (k1_relat_1 @ X28) @ X29)
% 0.77/0.95          | ~ (v1_funct_1 @ X28)
% 0.77/0.95          | ~ (v1_relat_1 @ X28))),
% 0.77/0.95      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.77/0.95  thf('45', plain,
% 0.77/0.95      ((~ (v1_relat_1 @ sk_D)
% 0.77/0.95        | ~ (v1_funct_1 @ sk_D)
% 0.77/0.95        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C))),
% 0.77/0.95      inference('sup-', [status(thm)], ['43', '44'])).
% 0.77/0.95  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.77/0.95      inference('sup-', [status(thm)], ['13', '14'])).
% 0.77/0.95  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('48', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.77/0.95      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.77/0.95  thf('49', plain,
% 0.77/0.95      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.77/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.77/0.95      inference('sup+', [status(thm)], ['42', '48'])).
% 0.77/0.95  thf('50', plain,
% 0.77/0.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.77/0.95      inference('split', [status(esa)], ['5'])).
% 0.77/0.95  thf('51', plain,
% 0.77/0.95      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.77/0.95         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.77/0.95      inference('split', [status(esa)], ['0'])).
% 0.77/0.95  thf('52', plain,
% 0.77/0.95      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.77/0.95         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['50', '51'])).
% 0.77/0.95  thf('53', plain,
% 0.77/0.95      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['49', '52'])).
% 0.77/0.95  thf('54', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.77/0.95      inference('split', [status(esa)], ['5'])).
% 0.77/0.95  thf(d1_funct_2, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i]:
% 0.77/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.95       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.77/0.95           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.77/0.95             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.77/0.95         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.77/0.95           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.77/0.95             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.77/0.95  thf(zf_stmt_1, axiom,
% 0.77/0.95    (![B:$i,A:$i]:
% 0.77/0.95     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.77/0.95       ( zip_tseitin_0 @ B @ A ) ))).
% 0.77/0.95  thf('55', plain,
% 0.77/0.95      (![X20 : $i, X21 : $i]:
% 0.77/0.95         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.77/0.95  thf('56', plain,
% 0.77/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.77/0.95  thf(zf_stmt_3, axiom,
% 0.77/0.95    (![C:$i,B:$i,A:$i]:
% 0.77/0.95     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.77/0.95       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.77/0.95  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.77/0.95  thf(zf_stmt_5, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i]:
% 0.77/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.95       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.77/0.95         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.77/0.95           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.77/0.95             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.77/0.95  thf('57', plain,
% 0.77/0.95      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.77/0.95         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.77/0.95          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.77/0.95          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.77/0.95  thf('58', plain,
% 0.77/0.95      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.77/0.95      inference('sup-', [status(thm)], ['56', '57'])).
% 0.77/0.95  thf('59', plain,
% 0.77/0.95      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.77/0.95      inference('sup-', [status(thm)], ['55', '58'])).
% 0.77/0.95  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('61', plain,
% 0.77/0.95      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.77/0.95         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.77/0.95          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.77/0.95          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.77/0.95  thf('62', plain,
% 0.77/0.95      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.77/0.95        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['60', '61'])).
% 0.77/0.95  thf('63', plain,
% 0.77/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf(redefinition_k1_relset_1, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i]:
% 0.77/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.95       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.77/0.95  thf('64', plain,
% 0.77/0.95      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.77/0.95         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.77/0.95          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.77/0.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.77/0.95  thf('65', plain,
% 0.77/0.95      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.77/0.95      inference('sup-', [status(thm)], ['63', '64'])).
% 0.77/0.95  thf('66', plain,
% 0.77/0.95      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.77/0.95      inference('demod', [status(thm)], ['62', '65'])).
% 0.77/0.95  thf('67', plain,
% 0.77/0.95      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['59', '66'])).
% 0.77/0.95  thf('68', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.77/0.95      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.77/0.95  thf('69', plain,
% 0.77/0.95      (((v1_funct_2 @ sk_D @ sk_A @ sk_C) | ((sk_B) = (k1_xboole_0)))),
% 0.77/0.95      inference('sup+', [status(thm)], ['67', '68'])).
% 0.77/0.95  thf('70', plain,
% 0.77/0.95      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.77/0.95         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.77/0.95      inference('split', [status(esa)], ['0'])).
% 0.77/0.95  thf('71', plain,
% 0.77/0.95      ((((sk_B) = (k1_xboole_0))) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['69', '70'])).
% 0.77/0.95  thf('72', plain,
% 0.77/0.95      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.77/0.95      inference('split', [status(esa)], ['5'])).
% 0.77/0.95  thf('73', plain,
% 0.77/0.95      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.77/0.95         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.77/0.95             ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['71', '72'])).
% 0.77/0.95  thf('74', plain,
% 0.77/0.95      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | (((sk_B) = (k1_xboole_0)))),
% 0.77/0.95      inference('simplify', [status(thm)], ['73'])).
% 0.77/0.95  thf('75', plain,
% 0.77/0.95      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.77/0.95       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 0.77/0.95      inference('split', [status(esa)], ['0'])).
% 0.77/0.95  thf('76', plain,
% 0.77/0.95      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.77/0.95      inference('sat_resolution*', [status(thm)],
% 0.77/0.95                ['4', '41', '53', '54', '74', '75'])).
% 0.77/0.95  thf('77', plain,
% 0.77/0.95      (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.77/0.95      inference('simpl_trail', [status(thm)], ['1', '76'])).
% 0.77/0.95  thf('78', plain,
% 0.77/0.95      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['59', '66'])).
% 0.77/0.95  thf('79', plain,
% 0.77/0.95      ((m1_subset_1 @ sk_D @ 
% 0.77/0.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 0.77/0.95      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.77/0.95  thf('80', plain,
% 0.77/0.95      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.77/0.95        | ((sk_B) = (k1_xboole_0)))),
% 0.77/0.95      inference('sup+', [status(thm)], ['78', '79'])).
% 0.77/0.95  thf('81', plain,
% 0.77/0.95      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.77/0.95      inference('split', [status(esa)], ['5'])).
% 0.77/0.95  thf('82', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.77/0.95      inference('sat_resolution*', [status(thm)], ['4', '41', '53', '75', '54'])).
% 0.77/0.95  thf('83', plain, (((sk_B) != (k1_xboole_0))),
% 0.77/0.95      inference('simpl_trail', [status(thm)], ['81', '82'])).
% 0.77/0.95  thf('84', plain,
% 0.77/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.77/0.95      inference('simplify_reflect-', [status(thm)], ['80', '83'])).
% 0.77/0.95  thf('85', plain, ($false), inference('demod', [status(thm)], ['77', '84'])).
% 0.77/0.95  
% 0.77/0.95  % SZS output end Refutation
% 0.77/0.95  
% 0.77/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
