%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iGcJy9619b

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:11 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 537 expanded)
%              Number of leaves         :   35 ( 166 expanded)
%              Depth                    :   16
%              Number of atoms          :  856 (7702 expanded)
%              Number of equality atoms :   67 ( 438 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X4: $i,X5: $i] :
      ( ~ ( v4_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('23',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t218_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v5_relat_1 @ C @ A ) )
         => ( v5_relat_1 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v5_relat_1 @ X8 @ X9 )
      | ( v5_relat_1 @ X8 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t218_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ X0 @ sk_C )
      | ~ ( v5_relat_1 @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v5_relat_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('29',plain,(
    v5_relat_1 @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('33',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X35 ) @ X36 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('37',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','38'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('41',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('45',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf('46',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ( v1_funct_2 @ X35 @ ( k1_relat_1 @ X35 ) @ X36 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('49',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','50'])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('53',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
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

thf('57',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('64',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('66',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('67',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('71',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('75',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['4','43','55','56','76','77'])).

thf('79',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','78'])).

thf('80',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('82',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('84',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','43','55','77','56'])).

thf('85',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['82','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['79','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iGcJy9619b
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.66/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.66/0.89  % Solved by: fo/fo7.sh
% 0.66/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.89  % done 594 iterations in 0.446s
% 0.66/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.66/0.89  % SZS output start Refutation
% 0.66/0.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.66/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.89  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.66/0.89  thf(sk_D_type, type, sk_D: $i).
% 0.66/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.66/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.66/0.89  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.66/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.89  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.66/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.66/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.66/0.89  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.66/0.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.66/0.89  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.66/0.89  thf(t9_funct_2, conjecture,
% 0.66/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.89     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.66/0.89         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.89       ( ( r1_tarski @ B @ C ) =>
% 0.66/0.89         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.66/0.89           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.66/0.89             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.66/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.89    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.89        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.66/0.89            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.89          ( ( r1_tarski @ B @ C ) =>
% 0.66/0.89            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.66/0.89              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.66/0.89                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.66/0.89    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.66/0.89  thf('0', plain,
% 0.66/0.89      ((~ (v1_funct_1 @ sk_D)
% 0.66/0.89        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.66/0.89        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('1', plain,
% 0.66/0.89      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.66/0.89         <= (~
% 0.66/0.89             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.66/0.89      inference('split', [status(esa)], ['0'])).
% 0.66/0.89  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.66/0.89      inference('split', [status(esa)], ['0'])).
% 0.66/0.89  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.66/0.89      inference('sup-', [status(thm)], ['2', '3'])).
% 0.66/0.89  thf('5', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('6', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.66/0.89      inference('split', [status(esa)], ['5'])).
% 0.66/0.89  thf('7', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('8', plain,
% 0.66/0.89      (((m1_subset_1 @ sk_D @ 
% 0.66/0.89         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.66/0.89         <= ((((sk_A) = (k1_xboole_0))))),
% 0.66/0.89      inference('sup+', [status(thm)], ['6', '7'])).
% 0.66/0.89  thf(cc2_relset_1, axiom,
% 0.66/0.89    (![A:$i,B:$i,C:$i]:
% 0.66/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.89       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.66/0.89  thf('9', plain,
% 0.66/0.89      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.66/0.89         ((v4_relat_1 @ X14 @ X15)
% 0.66/0.89          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.66/0.89      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.66/0.89  thf('10', plain,
% 0.66/0.89      (((v4_relat_1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.66/0.89      inference('sup-', [status(thm)], ['8', '9'])).
% 0.66/0.89  thf(d18_relat_1, axiom,
% 0.66/0.89    (![A:$i,B:$i]:
% 0.66/0.89     ( ( v1_relat_1 @ B ) =>
% 0.66/0.89       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.66/0.89  thf('11', plain,
% 0.66/0.89      (![X4 : $i, X5 : $i]:
% 0.66/0.89         (~ (v4_relat_1 @ X4 @ X5)
% 0.66/0.89          | (r1_tarski @ (k1_relat_1 @ X4) @ X5)
% 0.66/0.89          | ~ (v1_relat_1 @ X4))),
% 0.66/0.89      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.66/0.89  thf('12', plain,
% 0.66/0.89      (((~ (v1_relat_1 @ sk_D)
% 0.66/0.89         | (r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0)))
% 0.66/0.89         <= ((((sk_A) = (k1_xboole_0))))),
% 0.66/0.89      inference('sup-', [status(thm)], ['10', '11'])).
% 0.66/0.89  thf('13', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf(cc1_relset_1, axiom,
% 0.66/0.89    (![A:$i,B:$i,C:$i]:
% 0.66/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.89       ( v1_relat_1 @ C ) ))).
% 0.66/0.89  thf('14', plain,
% 0.66/0.89      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.66/0.89         ((v1_relat_1 @ X11)
% 0.66/0.89          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.66/0.89      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.66/0.89  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.66/0.89      inference('sup-', [status(thm)], ['13', '14'])).
% 0.66/0.89  thf('16', plain,
% 0.66/0.89      (((r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0))
% 0.66/0.89         <= ((((sk_A) = (k1_xboole_0))))),
% 0.66/0.89      inference('demod', [status(thm)], ['12', '15'])).
% 0.66/0.89  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.66/0.89  thf('17', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.66/0.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.66/0.89  thf(d10_xboole_0, axiom,
% 0.66/0.89    (![A:$i,B:$i]:
% 0.66/0.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.66/0.89  thf('18', plain,
% 0.66/0.89      (![X0 : $i, X2 : $i]:
% 0.66/0.89         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.66/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.89  thf('19', plain,
% 0.66/0.89      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['17', '18'])).
% 0.66/0.89  thf('20', plain,
% 0.66/0.89      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.66/0.89      inference('sup-', [status(thm)], ['16', '19'])).
% 0.66/0.89  thf('21', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('22', plain,
% 0.66/0.89      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.66/0.89         ((v5_relat_1 @ X14 @ X16)
% 0.66/0.89          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.66/0.89      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.66/0.89  thf('23', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.66/0.89      inference('sup-', [status(thm)], ['21', '22'])).
% 0.66/0.89  thf('24', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf(t218_relat_1, axiom,
% 0.66/0.89    (![A:$i,B:$i]:
% 0.66/0.89     ( ( r1_tarski @ A @ B ) =>
% 0.66/0.89       ( ![C:$i]:
% 0.66/0.89         ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) ) =>
% 0.66/0.89           ( v5_relat_1 @ C @ B ) ) ) ))).
% 0.66/0.89  thf('25', plain,
% 0.66/0.89      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.66/0.89         (~ (v1_relat_1 @ X8)
% 0.66/0.89          | ~ (v5_relat_1 @ X8 @ X9)
% 0.66/0.89          | (v5_relat_1 @ X8 @ X10)
% 0.66/0.89          | ~ (r1_tarski @ X9 @ X10))),
% 0.66/0.89      inference('cnf', [status(esa)], [t218_relat_1])).
% 0.66/0.89  thf('26', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         ((v5_relat_1 @ X0 @ sk_C)
% 0.66/0.89          | ~ (v5_relat_1 @ X0 @ sk_B)
% 0.66/0.89          | ~ (v1_relat_1 @ X0))),
% 0.66/0.89      inference('sup-', [status(thm)], ['24', '25'])).
% 0.66/0.89  thf('27', plain, ((~ (v1_relat_1 @ sk_D) | (v5_relat_1 @ sk_D @ sk_C))),
% 0.66/0.89      inference('sup-', [status(thm)], ['23', '26'])).
% 0.66/0.89  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 0.66/0.89      inference('sup-', [status(thm)], ['13', '14'])).
% 0.66/0.89  thf('29', plain, ((v5_relat_1 @ sk_D @ sk_C)),
% 0.66/0.89      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.89  thf(d19_relat_1, axiom,
% 0.66/0.89    (![A:$i,B:$i]:
% 0.66/0.89     ( ( v1_relat_1 @ B ) =>
% 0.66/0.89       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.66/0.89  thf('30', plain,
% 0.66/0.89      (![X6 : $i, X7 : $i]:
% 0.66/0.89         (~ (v5_relat_1 @ X6 @ X7)
% 0.66/0.89          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.66/0.89          | ~ (v1_relat_1 @ X6))),
% 0.66/0.89      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.66/0.89  thf('31', plain,
% 0.66/0.89      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C))),
% 0.66/0.89      inference('sup-', [status(thm)], ['29', '30'])).
% 0.66/0.89  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.66/0.89      inference('sup-', [status(thm)], ['13', '14'])).
% 0.66/0.89  thf('33', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.66/0.89      inference('demod', [status(thm)], ['31', '32'])).
% 0.66/0.89  thf(t4_funct_2, axiom,
% 0.66/0.89    (![A:$i,B:$i]:
% 0.66/0.89     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.66/0.89       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.66/0.89         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.66/0.89           ( m1_subset_1 @
% 0.66/0.89             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.66/0.89  thf('34', plain,
% 0.66/0.89      (![X35 : $i, X36 : $i]:
% 0.66/0.89         (~ (r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 0.66/0.89          | (m1_subset_1 @ X35 @ 
% 0.66/0.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X35) @ X36)))
% 0.66/0.89          | ~ (v1_funct_1 @ X35)
% 0.66/0.89          | ~ (v1_relat_1 @ X35))),
% 0.66/0.89      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.66/0.89  thf('35', plain,
% 0.66/0.89      ((~ (v1_relat_1 @ sk_D)
% 0.66/0.89        | ~ (v1_funct_1 @ sk_D)
% 0.66/0.89        | (m1_subset_1 @ sk_D @ 
% 0.66/0.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C))))),
% 0.66/0.89      inference('sup-', [status(thm)], ['33', '34'])).
% 0.66/0.89  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 0.66/0.89      inference('sup-', [status(thm)], ['13', '14'])).
% 0.66/0.89  thf('37', plain, ((v1_funct_1 @ sk_D)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('38', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_D @ 
% 0.66/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 0.66/0.89      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.66/0.89  thf('39', plain,
% 0.66/0.89      (((m1_subset_1 @ sk_D @ 
% 0.66/0.89         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.66/0.89         <= ((((sk_A) = (k1_xboole_0))))),
% 0.66/0.89      inference('sup+', [status(thm)], ['20', '38'])).
% 0.66/0.89  thf('40', plain,
% 0.66/0.89      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.66/0.89      inference('split', [status(esa)], ['5'])).
% 0.66/0.89  thf('41', plain,
% 0.66/0.89      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.66/0.89         <= (~
% 0.66/0.89             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.66/0.89      inference('split', [status(esa)], ['0'])).
% 0.66/0.89  thf('42', plain,
% 0.66/0.89      ((~ (m1_subset_1 @ sk_D @ 
% 0.66/0.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.66/0.89         <= (~
% 0.66/0.89             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.66/0.89             (((sk_A) = (k1_xboole_0))))),
% 0.66/0.89      inference('sup-', [status(thm)], ['40', '41'])).
% 0.66/0.89  thf('43', plain,
% 0.66/0.89      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.66/0.89       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.66/0.89      inference('sup-', [status(thm)], ['39', '42'])).
% 0.66/0.89  thf('44', plain,
% 0.66/0.89      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.66/0.89      inference('sup-', [status(thm)], ['16', '19'])).
% 0.66/0.89  thf('45', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.66/0.89      inference('demod', [status(thm)], ['31', '32'])).
% 0.66/0.89  thf('46', plain,
% 0.66/0.89      (![X35 : $i, X36 : $i]:
% 0.66/0.89         (~ (r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 0.66/0.89          | (v1_funct_2 @ X35 @ (k1_relat_1 @ X35) @ X36)
% 0.66/0.89          | ~ (v1_funct_1 @ X35)
% 0.66/0.89          | ~ (v1_relat_1 @ X35))),
% 0.66/0.89      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.66/0.89  thf('47', plain,
% 0.66/0.89      ((~ (v1_relat_1 @ sk_D)
% 0.66/0.89        | ~ (v1_funct_1 @ sk_D)
% 0.66/0.89        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C))),
% 0.66/0.89      inference('sup-', [status(thm)], ['45', '46'])).
% 0.66/0.89  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 0.66/0.89      inference('sup-', [status(thm)], ['13', '14'])).
% 0.66/0.89  thf('49', plain, ((v1_funct_1 @ sk_D)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('50', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.66/0.89      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.66/0.89  thf('51', plain,
% 0.66/0.89      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.66/0.89         <= ((((sk_A) = (k1_xboole_0))))),
% 0.66/0.89      inference('sup+', [status(thm)], ['44', '50'])).
% 0.66/0.89  thf('52', plain,
% 0.66/0.89      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.66/0.89      inference('split', [status(esa)], ['5'])).
% 0.66/0.89  thf('53', plain,
% 0.66/0.89      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.66/0.89         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.66/0.89      inference('split', [status(esa)], ['0'])).
% 0.66/0.89  thf('54', plain,
% 0.66/0.89      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.66/0.89         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.66/0.89      inference('sup-', [status(thm)], ['52', '53'])).
% 0.66/0.89  thf('55', plain,
% 0.66/0.89      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['51', '54'])).
% 0.66/0.89  thf('56', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.66/0.89      inference('split', [status(esa)], ['5'])).
% 0.66/0.89  thf(d1_funct_2, axiom,
% 0.66/0.89    (![A:$i,B:$i,C:$i]:
% 0.66/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.89       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.66/0.89           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.66/0.89             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.66/0.89         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.66/0.89           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.66/0.89             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.66/0.89  thf(zf_stmt_1, axiom,
% 0.66/0.89    (![B:$i,A:$i]:
% 0.66/0.89     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.66/0.89       ( zip_tseitin_0 @ B @ A ) ))).
% 0.66/0.89  thf('57', plain,
% 0.66/0.89      (![X27 : $i, X28 : $i]:
% 0.66/0.89         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.66/0.89  thf('58', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.66/0.89  thf(zf_stmt_3, axiom,
% 0.66/0.89    (![C:$i,B:$i,A:$i]:
% 0.66/0.89     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.66/0.89       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.66/0.89  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.66/0.89  thf(zf_stmt_5, axiom,
% 0.66/0.89    (![A:$i,B:$i,C:$i]:
% 0.66/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.89       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.66/0.89         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.66/0.89           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.66/0.89             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.66/0.89  thf('59', plain,
% 0.66/0.89      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.66/0.89         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.66/0.89          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.66/0.89          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.66/0.89  thf('60', plain,
% 0.66/0.89      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.66/0.89      inference('sup-', [status(thm)], ['58', '59'])).
% 0.66/0.89  thf('61', plain,
% 0.66/0.89      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.66/0.89      inference('sup-', [status(thm)], ['57', '60'])).
% 0.66/0.89  thf('62', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('63', plain,
% 0.66/0.89      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.66/0.89         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.66/0.89          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.66/0.89          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.66/0.89  thf('64', plain,
% 0.66/0.89      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.66/0.89        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['62', '63'])).
% 0.66/0.89  thf('65', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf(redefinition_k1_relset_1, axiom,
% 0.66/0.89    (![A:$i,B:$i,C:$i]:
% 0.66/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.89       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.66/0.89  thf('66', plain,
% 0.66/0.89      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.66/0.89         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.66/0.89          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.66/0.89      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.66/0.89  thf('67', plain,
% 0.66/0.89      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.66/0.89      inference('sup-', [status(thm)], ['65', '66'])).
% 0.66/0.89  thf('68', plain,
% 0.66/0.89      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.66/0.89      inference('demod', [status(thm)], ['64', '67'])).
% 0.66/0.89  thf('69', plain,
% 0.66/0.89      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['61', '68'])).
% 0.66/0.89  thf('70', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.66/0.89      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.66/0.89  thf('71', plain,
% 0.66/0.89      (((v1_funct_2 @ sk_D @ sk_A @ sk_C) | ((sk_B) = (k1_xboole_0)))),
% 0.66/0.89      inference('sup+', [status(thm)], ['69', '70'])).
% 0.66/0.89  thf('72', plain,
% 0.66/0.89      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.66/0.89         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.66/0.89      inference('split', [status(esa)], ['0'])).
% 0.66/0.89  thf('73', plain,
% 0.66/0.89      ((((sk_B) = (k1_xboole_0))) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['71', '72'])).
% 0.66/0.89  thf('74', plain,
% 0.66/0.89      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.66/0.89      inference('split', [status(esa)], ['5'])).
% 0.66/0.89  thf('75', plain,
% 0.66/0.89      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.66/0.89         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.66/0.89             ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['73', '74'])).
% 0.66/0.89  thf('76', plain,
% 0.66/0.89      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | (((sk_B) = (k1_xboole_0)))),
% 0.66/0.89      inference('simplify', [status(thm)], ['75'])).
% 0.66/0.89  thf('77', plain,
% 0.66/0.89      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.66/0.89       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 0.66/0.89      inference('split', [status(esa)], ['0'])).
% 0.66/0.89  thf('78', plain,
% 0.66/0.89      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.66/0.89      inference('sat_resolution*', [status(thm)],
% 0.66/0.89                ['4', '43', '55', '56', '76', '77'])).
% 0.66/0.89  thf('79', plain,
% 0.66/0.89      (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.66/0.89      inference('simpl_trail', [status(thm)], ['1', '78'])).
% 0.66/0.89  thf('80', plain,
% 0.66/0.89      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['61', '68'])).
% 0.66/0.89  thf('81', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_D @ 
% 0.66/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 0.66/0.89      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.66/0.89  thf('82', plain,
% 0.66/0.89      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.66/0.89        | ((sk_B) = (k1_xboole_0)))),
% 0.66/0.89      inference('sup+', [status(thm)], ['80', '81'])).
% 0.66/0.89  thf('83', plain,
% 0.66/0.89      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.66/0.89      inference('split', [status(esa)], ['5'])).
% 0.66/0.89  thf('84', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.66/0.89      inference('sat_resolution*', [status(thm)], ['4', '43', '55', '77', '56'])).
% 0.66/0.89  thf('85', plain, (((sk_B) != (k1_xboole_0))),
% 0.66/0.89      inference('simpl_trail', [status(thm)], ['83', '84'])).
% 0.66/0.89  thf('86', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.66/0.89      inference('simplify_reflect-', [status(thm)], ['82', '85'])).
% 0.66/0.89  thf('87', plain, ($false), inference('demod', [status(thm)], ['79', '86'])).
% 0.66/0.89  
% 0.66/0.89  % SZS output end Refutation
% 0.66/0.89  
% 0.66/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
