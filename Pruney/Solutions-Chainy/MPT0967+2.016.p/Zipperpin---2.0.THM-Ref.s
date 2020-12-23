%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bEuuWWfs0h

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:13 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 563 expanded)
%              Number of leaves         :   39 ( 182 expanded)
%              Depth                    :   20
%              Number of atoms          :  986 (6685 expanded)
%              Number of equality atoms :   77 ( 568 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf('0',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X23 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
            & ( v1_funct_2 @ D @ A @ C )
            & ( v1_funct_1 @ D ) )
          | ( ( A != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_1 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ A )
     => ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( zip_tseitin_1 @ B @ A )
          | ( zip_tseitin_0 @ D @ C @ A ) ) ) ) )).

thf('10',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( zip_tseitin_1 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ( zip_tseitin_0 @ X35 @ X36 @ X34 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X34 @ X33 @ X35 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ X0 )
      | ( zip_tseitin_0 @ sk_D @ X0 @ sk_A )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ( zip_tseitin_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ X0 )
      | ( zip_tseitin_0 @ sk_D @ X0 @ sk_A )
      | ( zip_tseitin_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ sk_D @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( zip_tseitin_0 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['18'])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ sk_D @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('24',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( zip_tseitin_0 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['18'])).

thf('27',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('29',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('30',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = o_0_0_xboole_0 )
      | ~ ( zip_tseitin_1 @ X31 @ X32 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B = o_0_0_xboole_0 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('35',plain,
    ( ( sk_B != o_0_0_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('41',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('43',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('44',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ o_0_0_xboole_0 @ X9 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ o_0_0_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','44'])).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,
    ( ( r1_tarski @ sk_D @ o_0_0_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,
    ( ( ~ ( r1_tarski @ o_0_0_xboole_0 @ sk_D )
      | ( o_0_0_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('50',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('51',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('52',plain,(
    ! [X6: $i] :
      ( r1_tarski @ o_0_0_xboole_0 @ X6 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( o_0_0_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['55','56'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('61',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('62',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['54','65'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('67',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X27 )
      | ( v1_funct_2 @ X26 @ ( k1_relat_1 @ X26 ) @ X27 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['60','61'])).

thf('70',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( v1_funct_2 @ o_0_0_xboole_0 @ ( k1_relat_1 @ sk_D ) @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','71'])).

thf('73',plain,
    ( ( o_0_0_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','52'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('74',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('75',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('76',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('77',plain,
    ( ( k1_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( v1_funct_2 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73','77'])).

thf('79',plain,
    ( ( o_0_0_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('80',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('82',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['18'])).

thf('83',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( v1_funct_2 @ sk_D @ o_0_0_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ~ ( v1_funct_2 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','85'])).

thf('87',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ o_0_0_xboole_0 @ X9 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('89',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['18'])).

thf('90',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('92',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ o_0_0_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ o_0_0_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ o_0_0_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','44'])).

thf('95',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['18'])).

thf('97',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('98',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['22','86','95','96','97'])).

thf('99',plain,(
    sk_B != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['35','98'])).

thf('100',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['31','99'])).

thf('101',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['22','100','96'])).

thf('102',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(simpl_trail,[status(thm)],['19','101'])).

thf('103',plain,(
    zip_tseitin_1 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['17','102'])).

thf('104',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = o_0_0_xboole_0 )
      | ~ ( zip_tseitin_1 @ X31 @ X32 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('105',plain,(
    sk_B = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    sk_B != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['35','98'])).

thf('107',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['105','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bEuuWWfs0h
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:25:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 401 iterations in 0.138s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.38/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.38/0.60  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.38/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.60  thf(t9_funct_2, conjecture,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.60       ( ( r1_tarski @ B @ C ) =>
% 0.38/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.38/0.60           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.38/0.60             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.60            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.60          ( ( r1_tarski @ B @ C ) =>
% 0.38/0.60            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.38/0.60              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.38/0.60                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.38/0.60  thf('0', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('1', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(dt_k2_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.60         ((m1_subset_1 @ (k2_relset_1 @ X23 @ X24 @ X25) @ (k1_zfmisc_1 @ X24))
% 0.38/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ (k1_zfmisc_1 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.60  thf(t3_subset, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.60  thf('4', plain,
% 0.38/0.60      (![X12 : $i, X13 : $i]:
% 0.38/0.60         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.60  thf('5', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_B)),
% 0.38/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.60  thf(t1_xboole_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.38/0.60       ( r1_tarski @ A @ C ) ))).
% 0.38/0.60  thf('6', plain,
% 0.38/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.60         (~ (r1_tarski @ X3 @ X4)
% 0.38/0.60          | ~ (r1_tarski @ X4 @ X5)
% 0.38/0.60          | (r1_tarski @ X3 @ X5))),
% 0.38/0.60      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.38/0.60  thf('7', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ X0)
% 0.38/0.60          | ~ (r1_tarski @ sk_B @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.60  thf('8', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 0.38/0.60      inference('sup-', [status(thm)], ['0', '7'])).
% 0.38/0.60  thf('9', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(t8_funct_2, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.60         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.38/0.60       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.38/0.60         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.38/0.60             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 0.38/0.60           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.38/0.60  thf(zf_stmt_2, axiom,
% 0.38/0.60    (![B:$i,A:$i]:
% 0.38/0.60     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.38/0.60       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.38/0.60  thf(zf_stmt_4, axiom,
% 0.38/0.60    (![D:$i,C:$i,A:$i]:
% 0.38/0.60     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 0.38/0.60       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.38/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_5, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.60       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.38/0.60         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 0.38/0.60  thf('10', plain,
% 0.38/0.60      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.38/0.60         ((zip_tseitin_1 @ X33 @ X34)
% 0.38/0.60          | ~ (v1_funct_1 @ X35)
% 0.38/0.60          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.38/0.60          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.38/0.60          | (zip_tseitin_0 @ X35 @ X36 @ X34)
% 0.38/0.60          | ~ (r1_tarski @ (k2_relset_1 @ X34 @ X33 @ X35) @ X36))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ X0)
% 0.38/0.60          | (zip_tseitin_0 @ sk_D @ X0 @ sk_A)
% 0.38/0.60          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.38/0.60          | ~ (v1_funct_1 @ sk_D)
% 0.38/0.60          | (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.60  thf('12', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('13', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('14', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ X0)
% 0.38/0.60          | (zip_tseitin_0 @ sk_D @ X0 @ sk_A)
% 0.38/0.60          | (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.38/0.60  thf('15', plain,
% 0.38/0.60      (((zip_tseitin_1 @ sk_B @ sk_A) | (zip_tseitin_0 @ sk_D @ sk_C @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['8', '14'])).
% 0.38/0.60  thf('16', plain,
% 0.38/0.60      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.60         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.38/0.60          | ~ (zip_tseitin_0 @ X28 @ X29 @ X30))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.38/0.60  thf('17', plain,
% 0.38/0.60      (((zip_tseitin_1 @ sk_B @ sk_A)
% 0.38/0.60        | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.60  thf('18', plain,
% 0.38/0.60      ((~ (v1_funct_1 @ sk_D)
% 0.38/0.60        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.38/0.60        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('19', plain,
% 0.38/0.60      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.38/0.60         <= (~
% 0.38/0.60             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.38/0.60      inference('split', [status(esa)], ['18'])).
% 0.38/0.60  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('21', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.38/0.60      inference('split', [status(esa)], ['18'])).
% 0.38/0.60  thf('22', plain, (((v1_funct_1 @ sk_D))),
% 0.38/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      (((zip_tseitin_1 @ sk_B @ sk_A) | (zip_tseitin_0 @ sk_D @ sk_C @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['8', '14'])).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.60         ((v1_funct_2 @ X28 @ X30 @ X29) | ~ (zip_tseitin_0 @ X28 @ X29 @ X30))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      (((zip_tseitin_1 @ sk_B @ sk_A) | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.60  thf('26', plain,
% 0.38/0.60      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.38/0.60         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.38/0.60      inference('split', [status(esa)], ['18'])).
% 0.38/0.60  thf('27', plain,
% 0.38/0.60      (((zip_tseitin_1 @ sk_B @ sk_A))
% 0.38/0.60         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.60  thf('28', plain,
% 0.38/0.60      (![X31 : $i, X32 : $i]:
% 0.38/0.60         (((X31) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X31 @ X32))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.60  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.38/0.60  thf('29', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.60  thf('30', plain,
% 0.38/0.60      (![X31 : $i, X32 : $i]:
% 0.38/0.60         (((X31) = (o_0_0_xboole_0)) | ~ (zip_tseitin_1 @ X31 @ X32))),
% 0.38/0.60      inference('demod', [status(thm)], ['28', '29'])).
% 0.38/0.60  thf('31', plain,
% 0.38/0.60      ((((sk_B) = (o_0_0_xboole_0))) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['27', '30'])).
% 0.38/0.60  thf('32', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('33', plain,
% 0.38/0.60      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.38/0.60      inference('split', [status(esa)], ['32'])).
% 0.38/0.60  thf('34', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.60  thf('35', plain,
% 0.38/0.60      ((((sk_B) != (o_0_0_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['33', '34'])).
% 0.38/0.60  thf('36', plain,
% 0.38/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('split', [status(esa)], ['32'])).
% 0.38/0.60  thf('37', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('38', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_D @ 
% 0.38/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.38/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['36', '37'])).
% 0.38/0.60  thf('39', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.60  thf(t113_zfmisc_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.60  thf('40', plain,
% 0.38/0.60      (![X8 : $i, X9 : $i]:
% 0.38/0.60         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.60  thf('41', plain,
% 0.38/0.60      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['40'])).
% 0.38/0.60  thf('42', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.60  thf('43', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.60  thf('44', plain,
% 0.38/0.60      (![X9 : $i]: ((k2_zfmisc_1 @ o_0_0_xboole_0 @ X9) = (o_0_0_xboole_0))),
% 0.38/0.60      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.38/0.60  thf('45', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ o_0_0_xboole_0)))
% 0.38/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['38', '39', '44'])).
% 0.38/0.60  thf('46', plain,
% 0.38/0.60      (![X12 : $i, X13 : $i]:
% 0.38/0.60         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.60  thf('47', plain,
% 0.38/0.60      (((r1_tarski @ sk_D @ o_0_0_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.60  thf(d10_xboole_0, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.60  thf('48', plain,
% 0.38/0.60      (![X0 : $i, X2 : $i]:
% 0.38/0.60         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.60  thf('49', plain,
% 0.38/0.60      (((~ (r1_tarski @ o_0_0_xboole_0 @ sk_D) | ((o_0_0_xboole_0) = (sk_D))))
% 0.38/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.60  thf('50', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.38/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.60  thf('51', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.60  thf('52', plain, (![X6 : $i]: (r1_tarski @ o_0_0_xboole_0 @ X6)),
% 0.38/0.60      inference('demod', [status(thm)], ['50', '51'])).
% 0.38/0.60  thf('53', plain,
% 0.38/0.60      ((((o_0_0_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['49', '52'])).
% 0.38/0.60  thf('54', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('55', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(cc2_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.60  thf('56', plain,
% 0.38/0.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.60         ((v5_relat_1 @ X20 @ X22)
% 0.38/0.60          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.60  thf('57', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.38/0.60      inference('sup-', [status(thm)], ['55', '56'])).
% 0.38/0.60  thf(d19_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ B ) =>
% 0.38/0.60       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.60  thf('58', plain,
% 0.38/0.60      (![X15 : $i, X16 : $i]:
% 0.38/0.60         (~ (v5_relat_1 @ X15 @ X16)
% 0.38/0.60          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.38/0.60          | ~ (v1_relat_1 @ X15))),
% 0.38/0.60      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.38/0.60  thf('59', plain,
% 0.38/0.60      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['57', '58'])).
% 0.38/0.60  thf('60', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(cc1_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( v1_relat_1 @ C ) ))).
% 0.38/0.60  thf('61', plain,
% 0.38/0.60      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.60         ((v1_relat_1 @ X17)
% 0.38/0.60          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.60  thf('62', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.38/0.60  thf('63', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.38/0.60      inference('demod', [status(thm)], ['59', '62'])).
% 0.38/0.60  thf('64', plain,
% 0.38/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.60         (~ (r1_tarski @ X3 @ X4)
% 0.38/0.60          | ~ (r1_tarski @ X4 @ X5)
% 0.38/0.60          | (r1_tarski @ X3 @ X5))),
% 0.38/0.60      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.38/0.60  thf('65', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['63', '64'])).
% 0.38/0.60  thf('66', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.38/0.60      inference('sup-', [status(thm)], ['54', '65'])).
% 0.38/0.60  thf(t4_funct_2, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.60       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.38/0.60         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.38/0.60           ( m1_subset_1 @
% 0.38/0.60             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.38/0.60  thf('67', plain,
% 0.38/0.60      (![X26 : $i, X27 : $i]:
% 0.38/0.60         (~ (r1_tarski @ (k2_relat_1 @ X26) @ X27)
% 0.38/0.60          | (v1_funct_2 @ X26 @ (k1_relat_1 @ X26) @ X27)
% 0.38/0.60          | ~ (v1_funct_1 @ X26)
% 0.38/0.60          | ~ (v1_relat_1 @ X26))),
% 0.38/0.60      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.38/0.60  thf('68', plain,
% 0.38/0.60      ((~ (v1_relat_1 @ sk_D)
% 0.38/0.60        | ~ (v1_funct_1 @ sk_D)
% 0.38/0.60        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['66', '67'])).
% 0.38/0.60  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.38/0.60  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('71', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.38/0.60      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.38/0.60  thf('72', plain,
% 0.38/0.60      (((v1_funct_2 @ o_0_0_xboole_0 @ (k1_relat_1 @ sk_D) @ sk_C))
% 0.38/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['53', '71'])).
% 0.38/0.60  thf('73', plain,
% 0.38/0.60      ((((o_0_0_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['49', '52'])).
% 0.38/0.60  thf(t60_relat_1, axiom,
% 0.38/0.60    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.38/0.60     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.38/0.60  thf('74', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.38/0.60  thf('75', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.60  thf('76', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.60  thf('77', plain, (((k1_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.60      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.38/0.60  thf('78', plain,
% 0.38/0.60      (((v1_funct_2 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ sk_C))
% 0.38/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['72', '73', '77'])).
% 0.38/0.60  thf('79', plain,
% 0.38/0.60      ((((o_0_0_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['49', '52'])).
% 0.38/0.60  thf('80', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.60  thf('81', plain,
% 0.38/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('split', [status(esa)], ['32'])).
% 0.38/0.60  thf('82', plain,
% 0.38/0.60      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.38/0.60         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.38/0.60      inference('split', [status(esa)], ['18'])).
% 0.38/0.60  thf('83', plain,
% 0.38/0.60      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.38/0.60         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['81', '82'])).
% 0.38/0.60  thf('84', plain,
% 0.38/0.60      ((~ (v1_funct_2 @ sk_D @ o_0_0_xboole_0 @ sk_C))
% 0.38/0.60         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['80', '83'])).
% 0.38/0.60  thf('85', plain,
% 0.38/0.60      ((~ (v1_funct_2 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ sk_C))
% 0.38/0.60         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['79', '84'])).
% 0.38/0.60  thf('86', plain,
% 0.38/0.60      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['78', '85'])).
% 0.38/0.60  thf('87', plain,
% 0.38/0.60      (![X9 : $i]: ((k2_zfmisc_1 @ o_0_0_xboole_0 @ X9) = (o_0_0_xboole_0))),
% 0.38/0.60      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.38/0.60  thf('88', plain,
% 0.38/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('split', [status(esa)], ['32'])).
% 0.38/0.60  thf('89', plain,
% 0.38/0.60      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.38/0.60         <= (~
% 0.38/0.60             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.38/0.60      inference('split', [status(esa)], ['18'])).
% 0.38/0.60  thf('90', plain,
% 0.38/0.60      ((~ (m1_subset_1 @ sk_D @ 
% 0.38/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.38/0.60         <= (~
% 0.38/0.60             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.38/0.60             (((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['88', '89'])).
% 0.38/0.60  thf('91', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.60  thf('92', plain,
% 0.38/0.60      ((~ (m1_subset_1 @ sk_D @ 
% 0.38/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ o_0_0_xboole_0 @ sk_C))))
% 0.38/0.60         <= (~
% 0.38/0.60             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.38/0.60             (((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['90', '91'])).
% 0.38/0.60  thf('93', plain,
% 0.38/0.60      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ o_0_0_xboole_0)))
% 0.38/0.60         <= (~
% 0.38/0.60             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.38/0.60             (((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['87', '92'])).
% 0.38/0.60  thf('94', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ o_0_0_xboole_0)))
% 0.38/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['38', '39', '44'])).
% 0.38/0.60  thf('95', plain,
% 0.38/0.60      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.38/0.60       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.38/0.60      inference('demod', [status(thm)], ['93', '94'])).
% 0.38/0.60  thf('96', plain,
% 0.38/0.60      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.38/0.60       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 0.38/0.60      inference('split', [status(esa)], ['18'])).
% 0.38/0.60  thf('97', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.38/0.60      inference('split', [status(esa)], ['32'])).
% 0.38/0.60  thf('98', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.38/0.60      inference('sat_resolution*', [status(thm)],
% 0.38/0.60                ['22', '86', '95', '96', '97'])).
% 0.38/0.60  thf('99', plain, (((sk_B) != (o_0_0_xboole_0))),
% 0.38/0.60      inference('simpl_trail', [status(thm)], ['35', '98'])).
% 0.38/0.60  thf('100', plain, (((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.38/0.60      inference('simplify_reflect-', [status(thm)], ['31', '99'])).
% 0.38/0.60  thf('101', plain,
% 0.38/0.60      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.38/0.60      inference('sat_resolution*', [status(thm)], ['22', '100', '96'])).
% 0.38/0.60  thf('102', plain,
% 0.38/0.60      (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.38/0.60      inference('simpl_trail', [status(thm)], ['19', '101'])).
% 0.38/0.60  thf('103', plain, ((zip_tseitin_1 @ sk_B @ sk_A)),
% 0.38/0.60      inference('clc', [status(thm)], ['17', '102'])).
% 0.38/0.60  thf('104', plain,
% 0.38/0.60      (![X31 : $i, X32 : $i]:
% 0.38/0.60         (((X31) = (o_0_0_xboole_0)) | ~ (zip_tseitin_1 @ X31 @ X32))),
% 0.38/0.60      inference('demod', [status(thm)], ['28', '29'])).
% 0.38/0.60  thf('105', plain, (((sk_B) = (o_0_0_xboole_0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['103', '104'])).
% 0.38/0.60  thf('106', plain, (((sk_B) != (o_0_0_xboole_0))),
% 0.38/0.60      inference('simpl_trail', [status(thm)], ['35', '98'])).
% 0.38/0.60  thf('107', plain, ($false),
% 0.38/0.60      inference('simplify_reflect-', [status(thm)], ['105', '106'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
